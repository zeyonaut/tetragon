use super::symbol::*;
use crate::{
	interpreter::{base::*, cypress::*},
	utility::composite::apply_composed,
};

pub fn convert_variable_to_cps(variable: BaseVariable) -> CypressVariable {
	match variable {
		BaseVariable::Auto(x) => CypressVariable::Local(x),
		BaseVariable::Name(x) => CypressVariable::Name(x),
	}
}

pub fn convert_type_to_cps(base_ty: BaseType) -> CypressType {
	match base_ty {
		BaseType::Polarity => CypressType::Polarity,
		BaseType::Integer => CypressType::Integer,
		BaseType::Power { domain, codomain } => CypressType::Power {
			domain: Box::new(convert_type_to_cps((*domain).clone())),
			codomain: Box::new(convert_type_to_cps(*codomain)),
		},
		BaseType::Product(tys) => CypressType::Product(tys.into_iter().map(convert_type_to_cps).collect()),
	}
}

pub fn convert_expression_to_cps(
	base_term: BaseTerm,
	symbol_generator: &mut SymbolGenerator,
) -> Option<(CypressVariable, Box<dyn FnOnce(CypressTerm) -> CypressTerm>)> {
	let ty = base_term.ty();
	match base_term {
		BaseTerm::Polarity(x) => {
			let binding = symbol_generator.fresh();
			Some((
				CypressVariable::Local(binding),
				Box::new(move |rest| CypressTerm::AssignValue {
					binding,
					ty: CypressType::Polarity,
					value: CypressPrimitive::Polarity(x),
					rest: Box::new(rest),
				}),
			))
		},
		BaseTerm::Integer(x) => {
			let binding = symbol_generator.fresh();
			Some((
				CypressVariable::Local(binding),
				Box::new(move |rest| CypressTerm::AssignValue {
					binding,
					ty: CypressType::Integer,
					value: CypressPrimitive::Integer(x),
					rest: Box::new(rest),
				}),
			))
		},
		BaseTerm::Name(_, x) => {
			Some((convert_variable_to_cps(x), Box::new(core::convert::identity)))
		},
		BaseTerm::Tuple(parts) => {
			let binding = symbol_generator.fresh();

			let (part_variables, part_contexts): (Vec<_>, Vec<_>) = parts
				.into_iter()
				.map(|(_, term)| convert_expression_to_cps(term, symbol_generator))
				.collect::<Option<Vec<_>>>()?
				.into_iter()
				.unzip();
			Some((
				CypressVariable::Local(binding),
				Box::new(move |body| {
					apply_composed(
						part_contexts.into_iter().rev(),
						CypressTerm::AssignOperation {
							binding,
							operation: CypressOperation::Pair(part_variables.into_boxed_slice()),
							rest: Box::new(body),
						},
					)
				}),
			))
		},
		BaseTerm::Projection { ty: _, tuple, index } => {
			let binding = symbol_generator.fresh();

			let (tuple_variable, tuple_context) = convert_expression_to_cps(*tuple, symbol_generator)?;

			Some((
				CypressVariable::Local(binding),
				Box::new(move |body| {
					tuple_context(CypressTerm::AssignOperation {
						binding,
						operation: CypressOperation::Projection(tuple_variable, index),
						rest: Box::new(body),
					})
				}),
			))
		},
		BaseTerm::Function {
			fixpoint_name,
			parameter,
			domain,
			codomain,
			body,
		} => {
			let binding = symbol_generator.fresh();

			let body = convert_tail_expression_to_cps(*body, None, symbol_generator)?;

			let domain = convert_type_to_cps(domain.clone());
			let codomain = convert_type_to_cps(codomain.clone());

			Some((
				CypressVariable::Local(binding),
				Box::new(move |rest| CypressTerm::DeclareFunction {
					binding,
					fixpoint_name,
					domain,
					codomain,
					parameter,
					body: Box::new(body),
					rest: Box::new(rest),
				}),
			))
		},
		BaseTerm::Application {
			ty: _,
			function,
			argument,
		} => {
			// TODO: Handle intrinsic functions as operations instead. Maybe? Or how long can I delay the introduction of intrinsics?
			let outcome = symbol_generator.fresh();
			let continuation = symbol_generator.fresh();

			let (function_variable, function_context) = convert_expression_to_cps(*function, symbol_generator)?;
			let (argument_variable, argument_context) = convert_expression_to_cps(*argument, symbol_generator)?;

			let outcome_ty = convert_type_to_cps(ty);

			Some((
				CypressVariable::Local(outcome),
				Box::new(move |body| {
					function_context(argument_context(CypressTerm::DeclareContinuation {
						label: continuation,
						domain: outcome_ty,
						parameter: outcome,
						body: Box::new(body),
						rest: Box::new(CypressTerm::Apply {
							function: function_variable,
							continuation: Some(continuation),
							argument: argument_variable,
						}),
					}))
				}),
			))
		},
		BaseTerm::Assignment {
			ty: _,
			assignee,
			definition,
			rest,
		} => {
			let continuation = symbol_generator.fresh();

			let domain = convert_type_to_cps(definition.ty());

			let definition = convert_tail_expression_to_cps(*definition, Some(continuation), symbol_generator)?;
			let (rest_variable, rest_context) = convert_expression_to_cps(*rest, symbol_generator)?;

			Some((
				rest_variable.clone(),
				Box::new(move |body| CypressTerm::DeclareContinuation {
					label: continuation,
					domain,
					parameter: assignee,
					body: Box::new(rest_context(body)),
					rest: Box::new(definition),
				}),
			))
		},
		BaseTerm::EqualityQuery { left, right } => {
			let binding = symbol_generator.fresh();
			let (left_variable, left_context) = convert_expression_to_cps(*left, symbol_generator)?;
			let (right_variable, right_context) = convert_expression_to_cps(*right, symbol_generator)?;

			Some((
				CypressVariable::Local(binding),
				Box::new(move |body| {
					left_context(right_context(CypressTerm::AssignOperation {
						binding,
						operation: CypressOperation::EqualsQuery([left_variable, right_variable]),
						rest: Box::new(body),
					}))
				}),
			))
		},
		BaseTerm::CaseSplit { ty: _, scrutinee, cases } => {
			let outcome_continuation = symbol_generator.fresh();
			let outcome_parameter = symbol_generator.fresh();
			let yes_continuation = symbol_generator.fresh();
			let yes_parameter = symbol_generator.fresh();
			let no_continuation = symbol_generator.fresh();
			let no_parameter = symbol_generator.fresh();

			let mut yes_term = None;
			let mut no_term = None;
			for (pattern, body) in cases {
				if pattern {
					yes_term = Some(*body);
				} else {
					no_term = Some(*body);
				}
			}

			let yes_term = convert_tail_expression_to_cps(yes_term?, Some(outcome_continuation), symbol_generator)?;
			let no_term = convert_tail_expression_to_cps(no_term?, Some(outcome_continuation), symbol_generator)?;

			let (scrutinee_variable, scrutinee_context) = convert_expression_to_cps(*scrutinee, symbol_generator)?;

			let outcome_ty = convert_type_to_cps(ty);

			Some((
				CypressVariable::Local(outcome_parameter),
				Box::new(move |body| CypressTerm::DeclareContinuation {
					label: outcome_continuation,
					domain: outcome_ty,
					parameter: outcome_parameter,
					body: Box::new(body),
					rest: Box::new(CypressTerm::DeclareContinuation {
						label: yes_continuation,
						domain: CypressType::Unity,
						parameter: yes_parameter,
						body: Box::new(yes_term),
						rest: Box::new(CypressTerm::DeclareContinuation {
							label: no_continuation,
							domain: CypressType::Unity,
							parameter: no_parameter,
							body: Box::new(no_term),
							rest: Box::new(scrutinee_context(CypressTerm::CaseSplit {
								scrutinee: scrutinee_variable,
								yes_continuation,
								no_continuation,
							})),
						}),
					}),
				}),
			))
		},
	}
}

// A tail expression is essentially one that is immediately fed into a continuation.
// Making tail expressions a special case can lead to smaller CPS terms.
// Code will look very similar in many cases, except there is no translation context to be invoked; a continuation is called instead.
// TODO: I wonder if there's a way to refactor this to reduce code duplication?
pub fn convert_tail_expression_to_cps(
	base_term: BaseTerm,
	continuation_label: Option<CypressContinuationLabel>,
	symbol_generator: &mut SymbolGenerator,
) -> Option<CypressTerm> {
	match base_term {
		BaseTerm::Polarity(x) => {
			let binding = symbol_generator.fresh();

			Some(CypressTerm::AssignValue {
				binding,
				ty: CypressType::Polarity,
				value: CypressPrimitive::Polarity(x),
				rest: Box::new(CypressTerm::Continue {
					continuation_label,
					argument: CypressVariable::Local(binding),
				}),
			})
		},
		BaseTerm::Integer(x) => {
			let binding = symbol_generator.fresh();

			Some(CypressTerm::AssignValue {
				binding,
				ty: CypressType::Integer,
				value: CypressPrimitive::Integer(x),
				rest: Box::new(CypressTerm::Continue {
					continuation_label,
					argument: CypressVariable::Local(binding),
				}),
			})
		},
		BaseTerm::Name(_, argument) => Some(CypressTerm::Continue {
			continuation_label,
			argument: convert_variable_to_cps(argument),
		}),
		BaseTerm::Tuple(parts) => {
			let binding = symbol_generator.fresh();

			let (part_variables, part_contexts): (Vec<_>, Vec<_>) = parts
				.into_iter()
				.map(|(_, term)| convert_expression_to_cps(term, symbol_generator))
				.collect::<Option<Vec<_>>>()?
				.into_iter()
				.unzip();

			Some(apply_composed(
				part_contexts.into_iter().rev(),
				CypressTerm::AssignOperation {
					binding,
					operation: CypressOperation::Pair(part_variables.clone().into_boxed_slice()),
					rest: Box::new(CypressTerm::Continue {
						continuation_label,
						argument: CypressVariable::Local(binding),
					}),
				},
			))
		},
		BaseTerm::Projection { ty: _, tuple, index } => {
			let binding = symbol_generator.fresh();

			let (tuple_variable, tuple_context) = convert_expression_to_cps(*tuple, symbol_generator)?;

			Some(tuple_context(CypressTerm::AssignOperation {
				binding,
				operation: CypressOperation::Projection(tuple_variable.clone(), index),
				rest: Box::new(CypressTerm::Continue {
					continuation_label,
					argument: CypressVariable::Local(binding),
				}),
			}))
		},
		BaseTerm::Function {
			fixpoint_name,
			parameter,
			domain,
			codomain,
			body,
		} => {
			let binding = symbol_generator.fresh();

			Some(CypressTerm::DeclareFunction {
				binding,
				fixpoint_name,
				domain: convert_type_to_cps(domain),
				codomain: convert_type_to_cps(codomain),
				parameter: parameter,
				body: Box::new(convert_tail_expression_to_cps(*body, None, symbol_generator)?),
				rest: Box::new(CypressTerm::Continue {
					continuation_label,
					argument: CypressVariable::Local(binding),
				}),
			})
		},
		BaseTerm::Application {
			ty: _,
			function,
			argument,
		} => {
			let (function_variable, function_context) = convert_expression_to_cps(*function, symbol_generator)?;
			let (argument_variable, argument_context) = convert_expression_to_cps(*argument, symbol_generator)?;

			Some(function_context(argument_context(CypressTerm::Apply {
				function: function_variable,
				continuation: continuation_label,
				argument: argument_variable,
			})))
		},
		BaseTerm::Assignment {
			ty: _,
			assignee,
			definition,
			rest,
		} => {
			let inner_continuation_label = symbol_generator.fresh();

			Some(CypressTerm::DeclareContinuation {
				label: inner_continuation_label,
				domain: convert_type_to_cps(definition.ty()),
				parameter: assignee,
				body: Box::new(convert_tail_expression_to_cps(*rest, continuation_label, symbol_generator)?),
				rest: Box::new(convert_tail_expression_to_cps(
					*definition,
					Some(inner_continuation_label),
					symbol_generator,
				)?),
			})
		},
		BaseTerm::EqualityQuery { left, right } => {
			let binding = symbol_generator.fresh();

			let (left_variable, left_context) = convert_expression_to_cps(*left, symbol_generator)?;
			let (right_variable, right_context) = convert_expression_to_cps(*right, symbol_generator)?;

			Some(left_context(right_context(CypressTerm::AssignOperation {
				binding,
				operation: CypressOperation::EqualsQuery([left_variable.clone(), right_variable.clone()]),
				rest: Box::new(CypressTerm::Continue {
					continuation_label,
					argument: CypressVariable::Local(binding),
				}),
			})))
		},
		BaseTerm::CaseSplit { ty: _, scrutinee, cases } => {
			let yes_continuation = symbol_generator.fresh();
			let yes_parameter = symbol_generator.fresh();
			let no_continuation = symbol_generator.fresh();
			let no_parameter = symbol_generator.fresh();

			let mut yes_term = None;
			let mut no_term = None;
			for (pattern, body) in cases {
				if pattern {
					yes_term = Some(*body);
				} else {
					no_term = Some(*body);
				}
			}
			let yes_term = yes_term?;
			let no_term = no_term?;

			let (scrutinee_variable, scrutinee_context) = convert_expression_to_cps(*scrutinee, symbol_generator)?;

			Some(CypressTerm::DeclareContinuation {
				label: yes_continuation,
				domain: CypressType::Unity,
				parameter: yes_parameter.clone(),
				body: Box::new(convert_tail_expression_to_cps(
					yes_term,
					continuation_label,
					symbol_generator,
				)?),
				rest: Box::new(CypressTerm::DeclareContinuation {
					label: no_continuation,
					domain: CypressType::Unity,
					parameter: no_parameter.clone(),
					body: Box::new(convert_tail_expression_to_cps(no_term, continuation_label, symbol_generator)?),
					rest: Box::new(scrutinee_context(CypressTerm::CaseSplit {
						scrutinee: scrutinee_variable.clone(),
						yes_continuation,
						no_continuation,
					})),
				}),
			})
		},
	}
}

pub fn convert_program_to_cps(base_term: BaseTerm, symbol_generator: &mut SymbolGenerator) -> Option<CypressTerm> {
	let (expression_variable, expression_context) = convert_expression_to_cps(base_term, symbol_generator)?;

	Some(expression_context(CypressTerm::Halt {
		argument: expression_variable,
	}))
}

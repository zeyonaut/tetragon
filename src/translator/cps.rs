use super::elaborator::*;
use crate::{interpreter::cypress::*, utility::composite::apply_composed};

pub struct SymbolGenerator(u64);

impl SymbolGenerator {
	pub fn fresh(&mut self) -> u64 {
		let symbol = self.0;
		self.0 += 1;
		symbol
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
	base_expression: BaseExpression,
	symbol_generator: &mut SymbolGenerator,
) -> Option<(CypressVariable, Box<dyn Fn(CypressTerm) -> CypressTerm>)> {
	let ty = base_expression.ty;
	match base_expression.term {
		BaseTerm::Polarity(x) => {
			let binding = CypressVariable::Auto(symbol_generator.fresh());
			Some((
				binding.clone(),
				Box::new(move |rest| CypressTerm::AssignValue {
					binding: binding.clone(),
					ty: CypressType::Polarity,
					value: CypressValue::Polarity(x),
					rest: Box::new(rest),
				}),
			))
		},
		BaseTerm::Integer(x) => {
			let binding = CypressVariable::Auto(symbol_generator.fresh());
			Some((
				binding.clone(),
				Box::new(move |rest| CypressTerm::AssignValue {
					binding: binding.clone(),
					ty: CypressType::Integer,
					value: CypressValue::Integer(x),
					rest: Box::new(rest),
				}),
			))
		},
		BaseTerm::Name(x) => {
			// TODO: Does it matter that this is not necessarily fresh?
			Some((CypressVariable::Name(x), Box::new(core::convert::identity)))
		},
		BaseTerm::Tuple(x) => {
			let binding = CypressVariable::Auto(symbol_generator.fresh());

			let (part_variables, part_contexts): (Vec<_>, Vec<_>) = x
				.into_iter()
				.map(|expression| convert_expression_to_cps(expression, symbol_generator))
				.collect::<Option<Vec<_>>>()?
				.into_iter()
				.unzip();
			Some((
				binding.clone(),
				Box::new(move |body| {
					apply_composed(
						part_contexts.iter().map(AsRef::as_ref).rev(),
						CypressTerm::AssignOperation {
							binding: binding.clone(),
							operation: CypressOperation::Pair(part_variables.clone().into_boxed_slice()),
							rest: Box::new(body),
						},
					)
				}),
			))
		},
		BaseTerm::Projection { tuple, index } => {
			let binding = CypressVariable::Auto(symbol_generator.fresh());

			let (tuple_variable, tuple_context) = convert_expression_to_cps(*tuple, symbol_generator)?;

			let outcome_ty = convert_type_to_cps(ty);

			Some((
				binding.clone(),
				Box::new(move |body| {
					tuple_context(CypressTerm::AssignOperation {
						binding: binding.clone(),
						//ty: outcome_ty.clone(),
						operation: CypressOperation::Projection(tuple_variable.clone(), index),
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
			let binding = CypressVariable::Auto(symbol_generator.fresh());
			let parameter = CypressVariable::Name(parameter);

			let (body_variable, body_context) = convert_expression_to_cps(*body, symbol_generator)?;

			let domain = convert_type_to_cps(domain.clone());
			let codomain = convert_type_to_cps(codomain.clone());

			Some((
				binding.clone(),
				Box::new(move |rest| CypressTerm::DeclareFunction {
					binding: binding.clone(),
					fixpoint_name: fixpoint_name.clone().map(|name| CypressVariable::Name(name)),
					domain: domain.clone(),
					codomain: codomain.clone(),
					parameter: parameter.clone(),
					body: Box::new(body_context(CypressTerm::Continue {
						label: None,
						argument: body_variable.clone(),
					})),
					rest: Box::new(rest),
				}),
			))
		},
		BaseTerm::Application { function, argument } => {
			// TODO: Handle intrinsic functions as operations instead. Maybe? Or how long can I delay the introduction of intrinsics?
			let outcome = CypressVariable::Auto(symbol_generator.fresh());
			let continuation = symbol_generator.fresh();

			let (function_variable, function_context) = convert_expression_to_cps(*function, symbol_generator)?;
			let (argument_variable, argument_context) = convert_expression_to_cps(*argument, symbol_generator)?;

			let outcome_ty = convert_type_to_cps(ty);

			Some((
				outcome.clone(),
				Box::new(move |body| {
					function_context(argument_context(CypressTerm::DeclareContinuation {
						label: continuation,
						domain: outcome_ty.clone(),
						parameter: outcome.clone(),
						body: Box::new(body),
						rest: Box::new(CypressTerm::Apply {
							function: function_variable.clone(),
							continuation,
							argument: argument_variable.clone(),
						}),
					}))
				}),
			))
		},
		BaseTerm::Assignment {
			assignee,
			definition,
			rest,
		} => {
			let continuation = symbol_generator.fresh();

			let (definition_variable, definition_context) = convert_expression_to_cps((*definition).clone(), symbol_generator)?;
			let (rest_variable, rest_context) = convert_expression_to_cps(*rest, symbol_generator)?;

			let domain = convert_type_to_cps(definition.ty.clone());

			Some((
				rest_variable.clone(),
				Box::new(move |body| CypressTerm::DeclareContinuation {
					label: continuation,
					domain: domain.clone(),
					parameter: CypressVariable::Name(assignee.clone()),
					body: Box::new(rest_context(body)),
					rest: Box::new(definition_context(CypressTerm::Continue {
						label: Some(continuation),
						argument: definition_variable.clone(),
					})),
				}),
			))
		},
		BaseTerm::EqualityQuery { left, right } => {
			let binding = CypressVariable::Auto(symbol_generator.fresh());
			let (left_variable, left_context) = convert_expression_to_cps(*left, symbol_generator)?;
			let (right_variable, right_context) = convert_expression_to_cps(*right, symbol_generator)?;

			Some((
				binding.clone(),
				Box::new(move |body| {
					left_context(right_context(CypressTerm::AssignOperation {
						binding: binding.clone(),
						//ty: CypressType::Polarity,
						operation: CypressOperation::EqualsQuery([left_variable.clone(), right_variable.clone()]),
						rest: Box::new(body),
					}))
				}),
			))
		},
		BaseTerm::CaseSplit { scrutinee, cases } => {
			let outcome_continuation = symbol_generator.fresh();
			let outcome_parameter = CypressVariable::Auto(symbol_generator.fresh());
			let yes_continuation = symbol_generator.fresh();
			let yes_parameter = CypressVariable::Auto(symbol_generator.fresh());
			let no_continuation = symbol_generator.fresh();
			let no_parameter = CypressVariable::Auto(symbol_generator.fresh());

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

			let (yes_variable, yes_context) = convert_expression_to_cps(yes_term, symbol_generator)?;
			let (no_variable, no_context) = convert_expression_to_cps(no_term, symbol_generator)?;
			let (scrutinee_variable, scrutinee_context) = convert_expression_to_cps(*scrutinee, symbol_generator)?;

			let outcome_ty = convert_type_to_cps(ty);

			Some((
				outcome_parameter.clone(),
				Box::new(move |body| CypressTerm::DeclareContinuation {
					label: outcome_continuation,
					domain: outcome_ty.clone(),
					parameter: outcome_parameter.clone(),
					body: Box::new(body),
					rest: Box::new(CypressTerm::DeclareContinuation {
						label: yes_continuation,
						domain: CypressType::Unity,
						parameter: yes_parameter.clone(),
						body: Box::new(yes_context(CypressTerm::Continue {
							label: Some(outcome_continuation),
							argument: yes_variable.clone(),
						})),
						rest: Box::new(CypressTerm::DeclareContinuation {
							label: no_continuation,
							domain: CypressType::Unity,
							parameter: no_parameter.clone(),
							body: Box::new(no_context(CypressTerm::Continue {
								label: Some(outcome_continuation),
								argument: no_variable.clone(),
							})),
							rest: Box::new(scrutinee_context(CypressTerm::CaseSplit {
								scrutinee: scrutinee_variable.clone(),
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

pub fn convert_program_to_cps(base_expression: BaseExpression) -> Option<CypressTerm> {
	let mut symbol_generator = SymbolGenerator(0);

	let (expression_variable, expression_context) = convert_expression_to_cps(base_expression, &mut symbol_generator)?;

	Some(expression_context(CypressTerm::Halt {
		argument: expression_variable,
	}))
}

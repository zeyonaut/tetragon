use super::label::*;
use crate::{
	interpreter::{base::*, cypress::*},
	utility::{composite::apply_composed, slice::match_slice},
};

pub fn convert_variable_to_cps(variable: BaseVariable) -> CypressProjection {
	CypressProjection::new(match variable {
		BaseVariable::Auto(x) => CypressVariable::Local(x),
		BaseVariable::Name(x) => CypressVariable::Global(x),
	})
}

pub fn convert_ty_to_cps(base_ty: BaseType) -> CypressType {
	match base_ty {
		BaseType::Empty => unimplemented!(),
		BaseType::Polarity => CypressType::Polarity,
		BaseType::Integer => CypressType::Integer,
		BaseType::Power { domain, codomain } => CypressType::Power {
			domain: Box::new(convert_ty_to_cps((*domain).clone())),
			codomain: Box::new(convert_ty_to_cps(*codomain)),
		},
		BaseType::Product(tys) => CypressType::Product(tys.into_iter().map(convert_ty_to_cps).collect()),
	}
}

#[derive(Clone)]
struct LoopStack {
	stepper_and_emitter_stack: Vec<(Label, Option<Label>)>,
}

impl LoopStack {
	pub fn new() -> Self {
		Self {
			stepper_and_emitter_stack: Vec::new(),
		}
	}

	pub fn push(&mut self, stepper: Label, emitter: Option<Label>) {
		self.stepper_and_emitter_stack.push((stepper, emitter));
	}

	pub fn pop(&mut self) {
		self.stepper_and_emitter_stack.pop().unwrap();
	}

	pub fn get_emitter(&self, stepper: &Label) -> Option<Option<Label>> {
		self.stepper_and_emitter_stack
			.iter()
			.rev()
			.find_map(|(s, e)| if s == stepper { Some(e.clone()) } else { None })
	}
}

fn convert_expression_to_cps(
	base_term: BaseTerm,
	loop_stack: &mut LoopStack,
	symbol_generator: &mut LabelGenerator,
) -> Option<(CypressProjection, Box<dyn FnOnce(CypressTerm) -> CypressTerm>)> {
	let ty = base_term.ty();
	match base_term {
		BaseTerm::Polarity(x) => {
			let [binding] = symbol_generator.fresh();
			Some((
				CypressProjection::new(CypressVariable::Local(binding)),
				Box::new(move |rest| {
					CypressStatement::AssignValue {
						binding,
						ty: CypressType::Polarity,
						value: CypressPrimitive::Polarity(x),
					}
					.prepend_to(rest)
				}),
			))
		},
		BaseTerm::Integer(x) => {
			let [binding] = symbol_generator.fresh();
			Some((
				CypressProjection::new(CypressVariable::Local(binding)),
				Box::new(move |rest| {
					CypressStatement::AssignValue {
						binding,
						ty: CypressType::Integer,
						value: CypressPrimitive::Integer(x),
					}
					.prepend_to(rest)
				}),
			))
		},
		BaseTerm::Name(_, x) => Some((convert_variable_to_cps(x), Box::new(core::convert::identity))),
		BaseTerm::Tuple(parts) => {
			let [binding] = symbol_generator.fresh();

			let (part_variables, part_contexts): (Vec<_>, Vec<_>) = parts
				.into_iter()
				.map(|(ty, term)| {
					let (projection, context) = convert_expression_to_cps(term, loop_stack, symbol_generator)?;
					Some(((convert_ty_to_cps(ty), projection), context))
				})
				.collect::<Option<Vec<_>>>()?
				.into_iter()
				.unzip();
			Some((
				CypressProjection::new(CypressVariable::Local(binding)),
				Box::new(move |body| {
					apply_composed(
						part_contexts.into_iter().rev(),
						CypressStatement::AssignOperation {
							binding,
							operation: CypressOperation::Pair(part_variables.into_boxed_slice()),
						}
						.prepend_to(body),
					)
				}),
			))
		},
		BaseTerm::Projection { ty, tuple, index } => {
			let [binding] = symbol_generator.fresh();

			let (tuple_variable, tuple_context) = convert_expression_to_cps(*tuple, loop_stack, symbol_generator)?;

			Some((
				CypressProjection::new(CypressVariable::Local(binding)),
				Box::new(move |body| {
					tuple_context(
						CypressStatement::AssignOperation {
							binding,
							operation: CypressOperation::Id(
								convert_ty_to_cps(ty),
								tuple_variable.project(CypressProjector::Field(index)),
							),
						}
						.prepend_to(body),
					)
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
			let [binding] = symbol_generator.fresh();

			let body = convert_tail_expression_to_cps(*body, None, loop_stack, symbol_generator)?;

			let domain = convert_ty_to_cps(domain.clone());
			let codomain = convert_ty_to_cps(codomain.clone());

			Some((
				CypressProjection::new(CypressVariable::Local(binding)),
				Box::new(move |rest| {
					CypressStatement::DeclareFunction {
						binding,
						fixpoint_name,
						domain,
						codomain,
						parameter,
						body: Box::new(body),
					}
					.prepend_to(rest)
				}),
			))
		},
		BaseTerm::Application {
			codomain,
			function,
			argument,
		} => {
			let domain = argument.ty();
			let [outcome, continuation] = symbol_generator.fresh();

			let (function_variable, function_context) = convert_expression_to_cps(*function, loop_stack, symbol_generator)?;
			let (argument_variable, argument_context) = convert_expression_to_cps(*argument, loop_stack, symbol_generator)?;

			let outcome_ty = convert_ty_to_cps(ty);

			Some((
				CypressProjection::new(CypressVariable::Local(outcome)),
				Box::new(move |body| {
					function_context(argument_context(
						CypressStatement::DeclareContinuation {
							label: continuation,
							domain: outcome_ty,
							parameter: outcome,
							body: Box::new(body),
						}
						.prepend_to(
							CypressTerminator::Apply {
								function: function_variable,
								domain: convert_ty_to_cps(domain),
								codomain: convert_ty_to_cps(codomain),
								continuation: Some(continuation),
								argument: argument_variable,
							}
							.into(),
						),
					))
				}),
			))
		},
		BaseTerm::IntrinsicInvocation { intrinsic, arguments } => match intrinsic {
			BaseIntrinsic::Add => {
				match_slice! { arguments.into_boxed_slice();
					[left, right] => {
						let [binding] = symbol_generator.fresh();
						let (left_variable, left_context) = convert_expression_to_cps(left, loop_stack, symbol_generator)?;
						let (right_variable, right_context) = convert_expression_to_cps(right, loop_stack, symbol_generator)?;
						Some((
							CypressProjection::new(CypressVariable::Local(binding)),
							Box::new(move |body| {
								left_context(right_context(CypressStatement::AssignOperation {
									binding,
									operation: CypressOperation::Add([left_variable, right_variable]),
								}.prepend_to(body)))
							}),
						))
					},
					_ => None,
				}
			},
		},
		BaseTerm::Assignment {
			ty: _,
			assignee,
			definition,
			rest,
		} => {
			let [continuation] = symbol_generator.fresh();

			let domain = convert_ty_to_cps(definition.ty());

			let definition = convert_tail_expression_to_cps(*definition, Some(continuation), loop_stack, symbol_generator)?;
			let (rest_variable, rest_context) = convert_expression_to_cps(*rest, loop_stack, symbol_generator)?;

			Some((
				rest_variable.clone(),
				Box::new(move |body| {
					CypressStatement::DeclareContinuation {
						label: continuation,
						domain,
						parameter: assignee,
						body: Box::new(rest_context(body)),
					}
					.prepend_to(definition)
				}),
			))
		},
		BaseTerm::EqualityQuery { ty, left, right } => {
			let [binding] = symbol_generator.fresh();
			let (left_variable, left_context) = convert_expression_to_cps(*left, loop_stack, symbol_generator)?;
			let (right_variable, right_context) = convert_expression_to_cps(*right, loop_stack, symbol_generator)?;

			Some((
				CypressProjection::new(CypressVariable::Local(binding)),
				Box::new(move |body| {
					left_context(right_context(
						CypressStatement::AssignOperation {
							binding,
							operation: CypressOperation::EqualsQuery(convert_ty_to_cps(ty), [left_variable, right_variable]),
						}
						.prepend_to(body),
					))
				}),
			))
		},
		BaseTerm::CaseSplit { ty: _, scrutinee, cases } => {
			let [outcome_continuation, outcome_parameter, yes_continuation, yes_parameter, no_continuation, no_parameter] =
				symbol_generator.fresh();

			let mut yes_term = None;
			let mut no_term = None;
			for (pattern, body) in cases {
				if pattern {
					yes_term = Some(*body);
				} else {
					no_term = Some(*body);
				}
			}

			let yes_term = convert_tail_expression_to_cps(yes_term?, Some(outcome_continuation), loop_stack, symbol_generator)?;
			let no_term = convert_tail_expression_to_cps(no_term?, Some(outcome_continuation), loop_stack, symbol_generator)?;

			let (scrutinee_variable, scrutinee_context) = convert_expression_to_cps(*scrutinee, loop_stack, symbol_generator)?;

			let outcome_ty = convert_ty_to_cps(ty);

			Some((
				CypressProjection::new(CypressVariable::Local(outcome_parameter)),
				Box::new(move |rest| {
					CypressTerm::compose(
						vec![
							CypressStatement::DeclareContinuation {
								label: outcome_continuation,
								domain: outcome_ty,
								parameter: outcome_parameter,
								body: Box::new(rest),
							},
							CypressStatement::DeclareContinuation {
								label: yes_continuation,
								domain: CypressType::Unity,
								parameter: yes_parameter,
								body: Box::new(yes_term),
							},
							CypressStatement::DeclareContinuation {
								label: no_continuation,
								domain: CypressType::Unity,
								parameter: no_parameter,
								body: Box::new(no_term),
							},
						],
						scrutinee_context(
							CypressTerminator::Branch {
								scrutinee: scrutinee_variable,
								yes_continuation,
								no_continuation,
							}
							.into(),
						),
					)
				}),
			))
		},
		BaseTerm::Loop {
			codomain,
			loop_name,
			parameter,
			argument,
			body,
		} => {
			let domain = convert_ty_to_cps(argument.ty());
			let codomain = convert_ty_to_cps(codomain);

			let (step_continuation, step_parameter) = (loop_name, parameter);
			let [emit_continuation, emit_parameter] = symbol_generator.fresh();

			loop_stack.push(step_continuation, Some(emit_continuation));
			let body_term = convert_tail_expression_to_cps(*body, Some(emit_continuation), loop_stack, symbol_generator)?;
			loop_stack.pop();
			let argument_term =
				convert_tail_expression_to_cps(*argument, Some(step_continuation), loop_stack, symbol_generator)?;

			Some((
				CypressProjection::new(CypressVariable::Local(emit_parameter)),
				Box::new(move |rest| {
					CypressTerm::compose(
						vec![
							CypressStatement::DeclareContinuation {
								label: emit_continuation,
								domain: codomain,
								parameter: emit_parameter,
								body: Box::new(rest),
							},
							CypressStatement::DeclareContinuation {
								label: step_continuation,
								domain: domain.clone(),
								parameter: step_parameter,
								body: Box::new(body_term),
							},
						],
						argument_term,
					)
				}),
			))
		},
		BaseTerm::Step { loop_name, argument } => {
			let step_continuation = loop_name;
			let argument_term =
				convert_tail_expression_to_cps(*argument, Some(step_continuation), loop_stack, symbol_generator)?;

			// NOTE: This variable should never get used, essentially.
			let [argument_variable] = symbol_generator.fresh();

			Some((
				CypressProjection::new(CypressVariable::Local(argument_variable)),
				Box::new(move |_| argument_term),
			))
		},
		BaseTerm::Emit { loop_name, argument } => {
			let emit_continuation = loop_stack.get_emitter(&loop_name)?;
			let argument_term = convert_tail_expression_to_cps(*argument, emit_continuation, loop_stack, symbol_generator)?;

			// NOTE: This variable should never get used, essentially.
			let [argument_variable] = symbol_generator.fresh();

			Some((
				CypressProjection::new(CypressVariable::Local(argument_variable)),
				Box::new(move |_| argument_term),
			))
		},
	}
}

// A tail expression is essentially one that is immediately fed into a continuation.
// Making tail expressions a special case can lead to smaller CPS terms.
// Code will look very similar in many cases, except there is no translation context to be invoked; a continuation is called instead.
fn convert_tail_expression_to_cps(
	base_term: BaseTerm,
	continuation_label: Option<Label>,
	loop_stack: &mut LoopStack,
	symbol_generator: &mut LabelGenerator,
) -> Option<CypressTerm> {
	match base_term {
		BaseTerm::Polarity(x) => {
			let [binding] = symbol_generator.fresh();

			Some(
				CypressStatement::AssignValue {
					binding,
					ty: CypressType::Polarity,
					value: CypressPrimitive::Polarity(x),
				}
				.prepend_to(
					CypressTerminator::Jump {
						continuation_label,
						argument: CypressProjection::new(CypressVariable::Local(binding)),
						domain: CypressType::Polarity,
					}
					.into(),
				),
			)
		},
		BaseTerm::Integer(x) => {
			let [binding] = symbol_generator.fresh();

			Some(
				CypressStatement::AssignValue {
					binding,
					ty: CypressType::Integer,
					value: CypressPrimitive::Integer(x),
				}
				.prepend_to(
					CypressTerminator::Jump {
						continuation_label,
						argument: CypressProjection::new(CypressVariable::Local(binding)),
						domain: CypressType::Integer,
					}
					.into(),
				),
			)
		},
		BaseTerm::Name(ty, argument) => Some(
			CypressTerminator::Jump {
				continuation_label,
				argument: convert_variable_to_cps(argument),
				domain: convert_ty_to_cps(ty),
			}
			.into(),
		),
		BaseTerm::Tuple(parts) => {
			let [binding] = symbol_generator.fresh();

			let (part_variables, part_contexts): (Vec<_>, Vec<_>) = parts
				.into_iter()
				.map(|(ty, term)| {
					let (projection, context) = convert_expression_to_cps(term, loop_stack, symbol_generator)?;
					Some(((convert_ty_to_cps(ty), projection), context))
				})
				.collect::<Option<Vec<_>>>()?
				.into_iter()
				.unzip();

			let part_tys = part_variables
				.iter()
				.map(|(ty, _)| ty.clone())
				.collect::<Vec<_>>()
				.into_boxed_slice();

			Some(apply_composed(
				part_contexts.into_iter().rev(),
				CypressStatement::AssignOperation {
					binding,
					operation: CypressOperation::Pair(part_variables.clone().into_boxed_slice()),
				}
				.prepend_to(
					CypressTerminator::Jump {
						continuation_label,
						argument: CypressProjection::new(CypressVariable::Local(binding)),
						domain: CypressType::Product(part_tys),
					}
					.into(),
				),
			))
		},
		BaseTerm::Projection { ty, tuple, index } => {
			let [binding] = symbol_generator.fresh();

			let (tuple_variable, tuple_context) = convert_expression_to_cps(*tuple, loop_stack, symbol_generator)?;

			let ty = convert_ty_to_cps(ty);

			Some(tuple_context(
				CypressStatement::AssignOperation {
					binding,
					operation: CypressOperation::Id(ty.clone(), tuple_variable.project(CypressProjector::Field(index))),
				}
				.prepend_to(
					CypressTerminator::Jump {
						continuation_label,
						argument: CypressProjection::new(CypressVariable::Local(binding)),
						domain: ty,
					}
					.into(),
				),
			))
		},
		BaseTerm::Function {
			fixpoint_name,
			parameter,
			domain,
			codomain,
			body,
		} => {
			let [binding] = symbol_generator.fresh();
			let domain = convert_ty_to_cps(domain);
			let codomain = convert_ty_to_cps(codomain);

			Some(
				CypressStatement::DeclareFunction {
					binding,
					fixpoint_name,
					domain: domain.clone(),
					codomain: codomain.clone(),
					parameter: parameter,
					body: Box::new(convert_tail_expression_to_cps(
						*body,
						None,
						&mut LoopStack::new(),
						symbol_generator,
					)?),
				}
				.prepend_to(
					CypressTerminator::Jump {
						continuation_label,
						argument: CypressProjection::new(CypressVariable::Local(binding)),
						domain: CypressType::Power {
							domain: Box::new(domain),
							codomain: Box::new(codomain),
						},
					}
					.into(),
				),
			)
		},
		BaseTerm::Application {
			codomain,
			function,
			argument,
		} => {
			let domain = argument.ty();

			let (function_variable, function_context) = convert_expression_to_cps(*function, loop_stack, symbol_generator)?;
			let (argument_variable, argument_context) = convert_expression_to_cps(*argument, loop_stack, symbol_generator)?;

			Some(function_context(argument_context(
				CypressTerminator::Apply {
					function: function_variable,
					domain: convert_ty_to_cps(domain),
					codomain: convert_ty_to_cps(codomain),
					continuation: continuation_label,
					argument: argument_variable,
				}
				.into(),
			)))
		},
		BaseTerm::IntrinsicInvocation { intrinsic, arguments } => match intrinsic {
			BaseIntrinsic::Add => {
				match_slice! { arguments.into_boxed_slice();
					[left, right] => {
						let [binding] = symbol_generator.fresh();
						let (left_variable, left_context) = convert_expression_to_cps(left, loop_stack, symbol_generator)?;
						let (right_variable, right_context) = convert_expression_to_cps(right, loop_stack, symbol_generator)?;
						Some(left_context(right_context(CypressStatement::AssignOperation {
							binding,
							operation: CypressOperation::Add([left_variable, right_variable]),
						}.prepend_to(CypressTerminator::Jump {
								continuation_label,
								argument: CypressProjection::new(CypressVariable::Local(binding)),
								domain: CypressType::Integer,
							}.into()))))
					},
					_ => None,
				}
			},
		},
		BaseTerm::Assignment {
			ty: _,
			assignee,
			definition,
			rest,
		} => {
			let [inner_continuation_label] = symbol_generator.fresh();

			Some(
				CypressStatement::DeclareContinuation {
					label: inner_continuation_label,
					domain: convert_ty_to_cps(definition.ty()),
					parameter: assignee,
					body: Box::new(convert_tail_expression_to_cps(
						*rest,
						continuation_label,
						loop_stack,
						symbol_generator,
					)?),
				}
				.prepend_to(convert_tail_expression_to_cps(
					*definition,
					Some(inner_continuation_label),
					loop_stack,
					symbol_generator,
				)?),
			)
		},
		BaseTerm::EqualityQuery { ty, left, right } => {
			let [binding] = symbol_generator.fresh();

			let (left_variable, left_context) = convert_expression_to_cps(*left, loop_stack, symbol_generator)?;
			let (right_variable, right_context) = convert_expression_to_cps(*right, loop_stack, symbol_generator)?;

			Some(left_context(right_context(
				CypressStatement::AssignOperation {
					binding,
					operation: CypressOperation::EqualsQuery(
						convert_ty_to_cps(ty),
						[left_variable.clone(), right_variable.clone()],
					),
				}
				.prepend_to(
					CypressTerminator::Jump {
						continuation_label,
						argument: CypressProjection::new(CypressVariable::Local(binding)),
						domain: CypressType::Polarity,
					}
					.into(),
				),
			)))
		},
		BaseTerm::CaseSplit { ty: _, scrutinee, cases } => {
			let [yes_continuation, yes_parameter, no_continuation, no_parameter] = symbol_generator.fresh();

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

			let (scrutinee_variable, scrutinee_context) = convert_expression_to_cps(*scrutinee, loop_stack, symbol_generator)?;

			Some(CypressTerm::compose(
				vec![
					CypressStatement::DeclareContinuation {
						label: yes_continuation,
						domain: CypressType::Unity,
						parameter: yes_parameter.clone(),
						body: Box::new(convert_tail_expression_to_cps(
							yes_term,
							continuation_label,
							loop_stack,
							symbol_generator,
						)?),
					},
					CypressStatement::DeclareContinuation {
						label: no_continuation,
						domain: CypressType::Unity,
						parameter: no_parameter.clone(),
						body: Box::new(convert_tail_expression_to_cps(
							no_term,
							continuation_label,
							loop_stack,
							symbol_generator,
						)?),
					},
				],
				scrutinee_context(
					CypressTerminator::Branch {
						scrutinee: scrutinee_variable.clone(),
						yes_continuation,
						no_continuation,
					}
					.into(),
				),
			))
		},
		BaseTerm::Loop {
			codomain: _,
			loop_name,
			parameter,
			argument,
			body,
		} => {
			let domain = convert_ty_to_cps(argument.ty());

			let emit_continuation = continuation_label;
			let (step_continuation, step_parameter) = (loop_name, parameter);

			loop_stack.push(step_continuation, emit_continuation);
			let body_term = convert_tail_expression_to_cps(*body, emit_continuation, loop_stack, symbol_generator)?;
			loop_stack.pop();
			let argument_term =
				convert_tail_expression_to_cps(*argument, Some(step_continuation), loop_stack, symbol_generator)?;

			Some(CypressTerm::compose(
				vec![CypressStatement::DeclareContinuation {
					label: step_continuation,
					domain: domain.clone(),
					parameter: step_parameter,
					body: Box::new(body_term),
				}],
				argument_term,
			))
		},
		BaseTerm::Step { loop_name, argument } => {
			let step_continuation = loop_name;

			convert_tail_expression_to_cps(*argument, Some(step_continuation), loop_stack, symbol_generator)
		},
		BaseTerm::Emit { loop_name, argument } => {
			let emit_continuation = loop_stack.get_emitter(&loop_name)?;

			convert_tail_expression_to_cps(*argument, emit_continuation, loop_stack, symbol_generator)
		},
	}
}

pub fn convert_program_to_cps(base_term: BaseTerm, symbol_generator: &mut LabelGenerator) -> Option<CypressTerm> {
	let domain = base_term.ty();
	let (expression_variable, expression_context) =
		convert_expression_to_cps(base_term, &mut LoopStack::new(), symbol_generator)?;

	Some(expression_context(
		CypressTerminator::Jump {
			continuation_label: None,
			argument: expression_variable,
			domain: convert_ty_to_cps(domain),
		}
		.into(),
	))
}

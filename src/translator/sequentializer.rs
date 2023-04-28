use std::collections::HashMap;

use super::label::{Label, LabelGenerator};
use crate::{
	interpreter::{
		base::BaseVariable,
		flow::{
			BinaryOperator, FlowOperand, FlowOperation, FlowPrimitive, FlowProcedure, FlowProgram, FlowProjection,
			FlowProjector, FlowStatement, FlowTerm, FlowTerminator, FlowType, FlowVariable,
		},
		june::{JuneIntrinsic, JunePrimitive, JuneProcedure, JuneProgram, JuneTerm, JuneType},
	},
	utility::{
		composite::apply_composed,
		ignore::Ignore,
		slice::{match_slice, slice},
	},
};

pub fn sequentialize(program: JuneProgram) -> FlowProgram {
	let JuneProgram {
		procedures,
		entry,
		mut symbol_generator,
	} = program;

	FlowProgram {
		procedures: procedures
			.into_iter()
			.map(|(label, procedure)| (label, sequentialize_procedure(procedure, &mut symbol_generator)))
			.collect(),
		entry,
		symbol_generator,
	}
}

fn sequentialize_procedure(procedure: JuneProcedure, symbol_generator: &mut LabelGenerator) -> FlowProcedure {
	use FlowOperand::*;
	use FlowTerminator::*;

	let JuneProcedure {
		domain,
		parameter,
		capture,
		body,
	} = procedure;

	let domain = sequentialize_ty(domain);
	let codomain = sequentialize_ty(body.ty());

	let (expression_variable, expression_context) = sequentialize_term(body, &mut LoopStack::new(), symbol_generator);

	let substitution = if let Some(parameter) = parameter {
		Substitution(HashMap::from([(
			parameter,
			FlowProjection::new(FlowVariable::Local(parameter)).project(FlowProjector::Parameter),
		)]))
	} else {
		Substitution(HashMap::new())
	};

	FlowProcedure {
		capture: capture.map(|(capture_label, factors)| {
			(
				capture_label,
				factors
					.into_iter()
					.map(sequentialize_ty)
					.collect::<Vec<_>>()
					.into_boxed_slice(),
			)
		}),
		parameter,
		domain,
		body: expression_context(
			Jump {
				continuation_label: None,
				domain: codomain.clone(),
				argument: expression_variable,
			}
			.into(),
		)
		.subbing(&substitution),
		codomain,
	}
}

fn sequentialize_ty(ty: JuneType) -> FlowType {
	match ty {
		JuneType::Empty => panic!("empty type"),
		JuneType::Unity => FlowType::Unity,
		JuneType::Polarity => FlowType::Polarity,
		JuneType::Integer => FlowType::Integer,
		JuneType::Product(factors) => FlowType::Product(
			factors
				.into_iter()
				.map(sequentialize_ty)
				.collect::<Vec<_>>()
				.into_boxed_slice(),
		),
		JuneType::Procedure { domain, codomain } => FlowType::Procedure,
		JuneType::Share(factors) => FlowType::Snapshot(factors.map(|factors| {
			factors
				.into_iter()
				.map(sequentialize_ty)
				.collect::<Vec<_>>()
				.into_boxed_slice()
		})),
	}
}

pub fn sequentialize_var(var: BaseVariable) -> FlowVariable {
	match var {
		BaseVariable::Auto(label) => FlowVariable::Local(label),
		BaseVariable::Name(label) => FlowVariable::Global(label),
	}
}

fn sequentialize_term(
	term: JuneTerm,
	loop_stack: &mut LoopStack,
	symbol_generator: &mut LabelGenerator,
) -> (FlowOperand, Box<dyn FnOnce(FlowTerm) -> FlowTerm>) {
	use JuneTerm::*;
	let ty = term.ty();
	match term {
		Primitive(primitive) => (
			FlowOperand::Constant(sequentialize_primitive(primitive)),
			Box::new(core::convert::identity),
		),
		Name(_, x) => (
			FlowOperand::Copy(FlowProjection::new(sequentialize_var(x))),
			Box::new(core::convert::identity),
		),
		Tuple(parts) => {
			let [binding] = symbol_generator.fresh();

			let (part_variables, part_contexts): (Vec<_>, Vec<_>) = parts
				.into_iter()
				.map(|(ty, term)| {
					let (projection, context) = sequentialize_term(term, loop_stack, symbol_generator);
					Some(((sequentialize_ty(ty), projection), context))
				})
				.collect::<Option<Vec<_>>>()
				.unwrap()
				.into_iter()
				.unzip();
			(
				FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(binding))),
				Box::new(move |body| {
					apply_composed(
						part_contexts.into_iter().rev(),
						FlowStatement::Assign {
							binding,
							operation: FlowOperation::Pair(part_variables.into_boxed_slice()),
						}
						.prepend_to(body),
					)
				}),
			)
		},
		Closure { procedure, fields, .. } => {
			let [binding] = symbol_generator.fresh();

			let (part_variables, part_contexts): (Vec<_>, Vec<_>) = fields
				.into_iter()
				.map(|term| {
					let ty = term.ty();
					let (projection, context) = sequentialize_term(term, loop_stack, symbol_generator);
					Some(((sequentialize_ty(ty), projection), context))
				})
				.collect::<Option<Vec<_>>>()
				.unwrap()
				.into_iter()
				.unzip();

			(
				FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(binding))),
				Box::new(move |body| {
					apply_composed(
						part_contexts.into_iter().rev(),
						FlowStatement::Assign {
							binding,
							operation: FlowOperation::Closure(
								FlowOperand::Constant(FlowPrimitive::Procedure(procedure)),
								part_variables.clone().into_boxed_slice(),
							),
						}
						.prepend_to(body),
					)
				}),
			)
		},
		Projection { ty, tuple, index } => {
			let (tuple_variable, tuple_context) = sequentialize_term(*tuple, loop_stack, symbol_generator);

			(tuple_variable.project(FlowProjector::Field(index)), tuple_context)
		},
		Free { ty, share, index } => {
			let (share_variable, share_context) = sequentialize_term(*share, loop_stack, symbol_generator);

			(share_variable.project(FlowProjector::Free(index)), share_context)
		},
		Application {
			codomain,
			function,
			argument,
		} => {
			let domain = argument.ty();
			let [outcome, continuation] = symbol_generator.fresh();

			let (function_variable, function_context) = sequentialize_term(*function, loop_stack, symbol_generator);
			let (argument_variable, argument_context) = sequentialize_term(*argument, loop_stack, symbol_generator);

			let outcome_ty = sequentialize_ty(ty);

			(
				FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(outcome))),
				Box::new(move |body| {
					function_context(argument_context(
						FlowStatement::DeclareContinuation {
							label: continuation,
							domain: outcome_ty,
							parameter: outcome,
							body,
						}
						.prepend_to(
							FlowTerminator::Apply {
								domain: sequentialize_ty(domain),
								codomain: sequentialize_ty(codomain),
								procedure: function_variable.clone().project(FlowProjector::Field(0)),
								snapshot: function_variable.project(FlowProjector::Field(1)),
								continuation_label: Some(continuation),
								argument: argument_variable,
							}
							.into(),
						),
					))
				}),
			)
		},
		IntrinsicInvocation { intrinsic, arguments } => match intrinsic {
			JuneIntrinsic::Add => {
				match_slice! { arguments.into_boxed_slice();
					[left, right] => {
						let [binding] = symbol_generator.fresh();
						let (left_variable, left_context) = sequentialize_term(left, loop_stack, symbol_generator);
						let (right_variable, right_context) = sequentialize_term(right, loop_stack, symbol_generator);
						(
							FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(binding))),
							Box::new(move |body| {
								left_context(right_context(FlowStatement::Assign {
									binding,
									operation: FlowOperation::Binary(BinaryOperator::Add, [left_variable, right_variable]),
								}.prepend_to(body)))
							}),
						)
					},
					_ => panic!("bad arguments"),
				}
			},
		},
		Assignment {
			ty: _,
			assignee,
			definition,
			rest,
		} => {
			let [continuation] = symbol_generator.fresh();

			let domain = sequentialize_ty(definition.ty());

			// FIXME: Substituting instead of generating a continuation jump prevents unnecessary reassignment or even assignment, but potentially generates expensive dereferences at each substitution site and, more importantly, delays drops that should happen at the moment of assignment due to scope exit. As such, the previous implementation is preserved here as a comment for reference until these issues are fixed.

			let definition = sequentialize_tail_term(*definition, Some(continuation), loop_stack, symbol_generator);
			let (rest_variable, rest_context) = sequentialize_term(*rest, loop_stack, symbol_generator);

			(
				rest_variable,
				Box::new(move |body| {
					FlowStatement::DeclareContinuation {
						label: continuation,
						domain,
						parameter: assignee,
						body: rest_context(body),
					}
					.prepend_to(definition)
				}),
			)

			/*
			let (definition_variable, definition_context) = sequentialize_term(*definition, loop_stack, symbol_generator);
			let (rest_variable, rest_context) = sequentialize_term(*rest, loop_stack, symbol_generator);

			let substitution = Substitution(HashMap::from([(assignee, definition_variable)]));

			(
				rest_variable,
				Box::new(move |body| definition_context(rest_context(body).subbing(&substitution))),
			)
			*/
		},
		EqualityQuery { ty, left, right } => {
			let [binding] = symbol_generator.fresh();
			let (left_variable, left_context) = sequentialize_term(*left, loop_stack, symbol_generator);
			let (right_variable, right_context) = sequentialize_term(*right, loop_stack, symbol_generator);

			(
				FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(binding))),
				Box::new(move |body| {
					left_context(right_context(
						FlowStatement::Assign {
							binding,
							operation: FlowOperation::Binary(
								BinaryOperator::EqualsQuery(sequentialize_ty(ty)),
								[left_variable, right_variable],
							),
						}
						.prepend_to(body),
					))
				}),
			)
		},
		CaseSplit { ty: _, scrutinee, cases } => {
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

			let yes_term = sequentialize_tail_term(yes_term.unwrap(), Some(outcome_continuation), loop_stack, symbol_generator);
			let no_term = sequentialize_tail_term(no_term.unwrap(), Some(outcome_continuation), loop_stack, symbol_generator);

			let (scrutinee_variable, scrutinee_context) = sequentialize_term(*scrutinee, loop_stack, symbol_generator);

			let outcome_ty = sequentialize_ty(ty);

			(
				FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(outcome_parameter))),
				Box::new(move |rest| {
					FlowTerm::compose(
						vec![
							FlowStatement::DeclareContinuation {
								label: outcome_continuation,
								domain: outcome_ty,
								parameter: outcome_parameter,
								body: rest,
							},
							FlowStatement::DeclareContinuation {
								label: yes_continuation,
								domain: FlowType::Unity,
								parameter: yes_parameter,
								body: yes_term,
							},
							FlowStatement::DeclareContinuation {
								label: no_continuation,
								domain: FlowType::Unity,
								parameter: no_parameter,
								body: no_term,
							},
						],
						scrutinee_context(
							FlowTerminator::Branch {
								scrutinee: scrutinee_variable,
								yes_continuation,
								no_continuation,
							}
							.into(),
						),
					)
				}),
			)
		},
		Loop {
			codomain,
			loop_name,
			parameter,
			argument,
			body,
		} => {
			let domain = sequentialize_ty(argument.ty());
			let codomain = sequentialize_ty(codomain);

			let (step_continuation, step_parameter) = (loop_name, parameter);
			let [emit_continuation, emit_parameter] = symbol_generator.fresh();

			loop_stack.push(step_continuation, Some(emit_continuation));
			let body_term = sequentialize_tail_term(*body, Some(emit_continuation), loop_stack, symbol_generator);
			loop_stack.pop();
			let argument_term = sequentialize_tail_term(*argument, Some(step_continuation), loop_stack, symbol_generator);

			(
				FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(emit_parameter))),
				Box::new(move |rest| {
					FlowTerm::compose(
						vec![
							FlowStatement::DeclareContinuation {
								label: emit_continuation,
								domain: codomain,
								parameter: emit_parameter,
								body: rest,
							},
							FlowStatement::DeclareContinuation {
								label: step_continuation,
								domain: domain.clone(),
								parameter: step_parameter,
								body: body_term,
							},
						],
						argument_term,
					)
				}),
			)
		},
		Step { loop_name, argument } => {
			let step_continuation = loop_name;
			let argument_term = sequentialize_tail_term(*argument, Some(step_continuation), loop_stack, symbol_generator);

			// NOTE: This variable should never get used, essentially.
			let [argument_variable] = symbol_generator.fresh();

			(
				FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(argument_variable))),
				Box::new(move |_| argument_term),
			)
		},
		Emit { loop_name, argument } => {
			let emit_continuation = loop_stack.get_emitter(&loop_name).unwrap();
			let argument_term = sequentialize_tail_term(*argument, emit_continuation, loop_stack, symbol_generator);

			// NOTE: This variable should never get used, essentially.
			let [argument_variable] = symbol_generator.fresh();

			(
				FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(argument_variable))),
				Box::new(move |_| argument_term),
			)
		},
	}
}

// A tail expression is essentially one that is immediately fed into a continuation.
// Making tail expressions a special case can lead to smaller CPS terms.
// Code will look very similar in many cases, except there is no translation context to be invoked; a continuation is called instead.
fn sequentialize_tail_term(
	term: JuneTerm,
	continuation_label: Option<Label>,
	loop_stack: &mut LoopStack,
	symbol_generator: &mut LabelGenerator,
) -> FlowTerm {
	use JuneTerm::*;
	match term {
		Primitive(primitive) => FlowTerminator::Jump {
			continuation_label,
			argument: FlowOperand::Constant(sequentialize_primitive(primitive)),
			domain: FlowType::Polarity,
		}
		.into(),
		Name(ty, argument) => FlowTerminator::Jump {
			continuation_label,
			argument: FlowOperand::Copy(FlowProjection::new(sequentialize_var(argument))),
			domain: sequentialize_ty(ty),
		}
		.into(),
		Tuple(parts) => {
			let [binding] = symbol_generator.fresh();

			let (part_variables, part_contexts): (Vec<_>, Vec<_>) = parts
				.into_iter()
				.map(|(ty, term)| {
					let (projection, context) = sequentialize_term(term, loop_stack, symbol_generator);
					Some(((sequentialize_ty(ty), projection), context))
				})
				.collect::<Option<Vec<_>>>()
				.unwrap()
				.into_iter()
				.unzip();

			let part_tys = part_variables
				.iter()
				.map(|(ty, _)| ty.clone())
				.collect::<Vec<_>>()
				.into_boxed_slice();

			apply_composed(
				part_contexts.into_iter().rev(),
				FlowStatement::Assign {
					binding,
					operation: FlowOperation::Pair(part_variables.clone().into_boxed_slice()),
				}
				.prepend_to(
					FlowTerminator::Jump {
						continuation_label,
						argument: FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(binding))),
						domain: FlowType::Product(part_tys),
					}
					.into(),
				),
			)
		},
		Closure { procedure, fields, .. } => {
			let [binding] = symbol_generator.fresh();

			let (part_variables, part_contexts): (Vec<_>, Vec<_>) = fields
				.into_iter()
				.map(|term| {
					let ty = term.ty();
					let (projection, context) = sequentialize_term(term, loop_stack, symbol_generator);
					Some(((sequentialize_ty(ty), projection), context))
				})
				.collect::<Option<Vec<_>>>()
				.unwrap()
				.into_iter()
				.unzip();

			apply_composed(
				part_contexts.into_iter().rev(),
				FlowStatement::Assign {
					binding,
					operation: FlowOperation::Closure(
						FlowOperand::Constant(FlowPrimitive::Procedure(procedure)),
						part_variables.clone().into_boxed_slice(),
					),
				}
				.prepend_to(
					FlowTerminator::Jump {
						continuation_label,
						argument: FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(binding))),
						domain: FlowType::Product(slice![FlowType::Procedure, FlowType::Snapshot(None)]),
					}
					.into(),
				),
			)
		},
		Projection { ty, tuple, index } => {
			let (tuple_variable, tuple_context) = sequentialize_term(*tuple, loop_stack, symbol_generator);

			let ty = sequentialize_ty(ty);

			tuple_context(
				FlowTerminator::Jump {
					continuation_label,
					argument: tuple_variable.project(FlowProjector::Field(index)),
					domain: ty,
				}
				.into(),
			)
		},
		Free { ty, share, index } => {
			let (share_variable, share_context) = sequentialize_term(*share, loop_stack, symbol_generator);

			let ty = sequentialize_ty(ty);

			share_context(
				FlowTerminator::Jump {
					continuation_label,
					argument: share_variable.project(FlowProjector::Free(index)),
					domain: ty,
				}
				.into(),
			)
		},
		Application {
			codomain,
			function,
			argument,
		} => {
			let domain = argument.ty();

			let (function_variable, function_context) = sequentialize_term(*function, loop_stack, symbol_generator);
			let (argument_variable, argument_context) = sequentialize_term(*argument, loop_stack, symbol_generator);

			function_context(argument_context(
				FlowTerminator::Apply {
					domain: sequentialize_ty(domain),
					codomain: sequentialize_ty(codomain),
					procedure: function_variable.clone().project(FlowProjector::Field(0)),
					snapshot: function_variable.project(FlowProjector::Field(1)),
					continuation_label,
					argument: argument_variable,
				}
				.into(),
			))
		},
		IntrinsicInvocation { intrinsic, arguments } => match intrinsic {
			JuneIntrinsic::Add => {
				match_slice! { arguments.into_boxed_slice();
					[left, right] => {
						let [binding] = symbol_generator.fresh();
						let (left_variable, left_context) = sequentialize_term(left, loop_stack, symbol_generator);
						let (right_variable, right_context) = sequentialize_term(right, loop_stack, symbol_generator);
						left_context(right_context(FlowStatement::Assign {
							binding,
							operation: FlowOperation::Binary(BinaryOperator::Add, [left_variable, right_variable]),
						}.prepend_to(FlowTerminator::Jump {
								continuation_label,
								argument: FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(binding))),
								domain: FlowType::Integer,
							}.into())))
					},
					_ => panic!("bad arguments"),
				}
			},
		},
		Assignment {
			ty: _,
			assignee,
			definition,
			rest,
		} => {
			let [inner_continuation_label] = symbol_generator.fresh();

			FlowStatement::DeclareContinuation {
				label: inner_continuation_label,
				domain: sequentialize_ty(definition.ty()),
				parameter: assignee,
				body: sequentialize_tail_term(*rest, continuation_label, loop_stack, symbol_generator),
			}
			.prepend_to(sequentialize_tail_term(
				*definition,
				Some(inner_continuation_label),
				loop_stack,
				symbol_generator,
			))
		},
		EqualityQuery { ty, left, right } => {
			let [binding] = symbol_generator.fresh();

			let (left_variable, left_context) = sequentialize_term(*left, loop_stack, symbol_generator);
			let (right_variable, right_context) = sequentialize_term(*right, loop_stack, symbol_generator);

			left_context(right_context(
				FlowStatement::Assign {
					binding,
					operation: FlowOperation::Binary(
						BinaryOperator::EqualsQuery(sequentialize_ty(ty)),
						[left_variable.clone(), right_variable.clone()],
					),
				}
				.prepend_to(
					FlowTerminator::Jump {
						continuation_label,
						argument: FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(binding))),
						domain: FlowType::Polarity,
					}
					.into(),
				),
			))
		},
		CaseSplit { ty: _, scrutinee, cases } => {
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
			let yes_term = yes_term.unwrap();
			let no_term = no_term.unwrap();

			let (scrutinee_variable, scrutinee_context) = sequentialize_term(*scrutinee, loop_stack, symbol_generator);

			FlowTerm::compose(
				vec![
					FlowStatement::DeclareContinuation {
						label: yes_continuation,
						domain: FlowType::Unity,
						parameter: yes_parameter,
						body: sequentialize_tail_term(yes_term, continuation_label, loop_stack, symbol_generator),
					},
					FlowStatement::DeclareContinuation {
						label: no_continuation,
						domain: FlowType::Unity,
						parameter: no_parameter,
						body: sequentialize_tail_term(no_term, continuation_label, loop_stack, symbol_generator),
					},
				],
				scrutinee_context(
					FlowTerminator::Branch {
						scrutinee: scrutinee_variable,
						yes_continuation,
						no_continuation,
					}
					.into(),
				),
			)
		},
		Loop {
			codomain: _,
			loop_name,
			parameter,
			argument,
			body,
		} => {
			let domain = sequentialize_ty(argument.ty());

			let emit_continuation = continuation_label;
			let (step_continuation, step_parameter) = (loop_name, parameter);

			loop_stack.push(step_continuation, emit_continuation);
			let body_term = sequentialize_tail_term(*body, emit_continuation, loop_stack, symbol_generator);
			loop_stack.pop();
			let argument_term = sequentialize_tail_term(*argument, Some(step_continuation), loop_stack, symbol_generator);

			FlowTerm::compose(
				vec![FlowStatement::DeclareContinuation {
					label: step_continuation,
					domain: domain.clone(),
					parameter: step_parameter,
					body: body_term,
				}],
				argument_term,
			)
		},
		Step { loop_name, argument } => {
			let step_continuation = loop_name;

			sequentialize_tail_term(*argument, Some(step_continuation), loop_stack, symbol_generator)
		},
		Emit { loop_name, argument } => {
			let emit_continuation = loop_stack.get_emitter(&loop_name).unwrap();

			sequentialize_tail_term(*argument, emit_continuation, loop_stack, symbol_generator)
		},
	}
}

fn sequentialize_primitive(primitive: JunePrimitive) -> FlowPrimitive {
	match primitive {
		JunePrimitive::Polarity(x) => FlowPrimitive::Polarity(x),
		JunePrimitive::Integer(x) => FlowPrimitive::Integer(x),
		JunePrimitive::Procedure { procedure, .. } => FlowPrimitive::Procedure(procedure),
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

struct Substitution(HashMap<Label, FlowProjection>);

trait Substitute {
	fn apply(&mut self, substitution: &Substitution);

	fn subbing(mut self, substitution: &Substitution) -> Self
	where
		Self: Sized,
	{
		self.apply(substitution);
		self
	}
}

impl Substitute for FlowProjection {
	fn apply(&mut self, substitution: &Substitution) {
		if let FlowVariable::Local(local) = self.root {
			if let Some(mut substituend) = substitution.0.get(&local).cloned() {
				substituend.projectors.append(&mut self.projectors);
				*self = substituend;
			}
		}
	}
}

impl Substitute for FlowOperand {
	fn apply(&mut self, substitution: &Substitution) {
		match self {
			FlowOperand::Copy(projection) => projection.apply(substitution),
			FlowOperand::Constant(_) => (),
		}
	}
}

impl Substitute for FlowOperation {
	fn apply(&mut self, substitution: &Substitution) {
		match self {
			FlowOperation::Id(_, operands) => operands.apply(substitution),
			FlowOperation::Binary(_, operands) => operands.iter_mut().map(|x| x.apply(substitution)).collect(),
			FlowOperation::Pair(operands) => operands.iter_mut().map(|(_, operand)| operand.apply(substitution)).collect(),
			FlowOperation::Closure(procedure, snapshot) => {
				procedure.apply(substitution);
				snapshot.iter_mut().map(|(_, x)| x.apply(substitution)).collect()
			},
		}
	}
}

impl Substitute for FlowTerm {
	fn apply(&mut self, substitution: &Substitution) {
		for statement in &mut self.statements {
			match statement {
				FlowStatement::Copy { projections } => {
					for projection in projections {
						projection.apply(substitution);
					}
				},
				// Drops should only occur for bound assignees, which are also fresh anyway.
				FlowStatement::Drop { .. } => (),
				FlowStatement::Assign { operation, .. } => operation.apply(substitution),
				// Because every parameter is fresh, we are not concerned about shadowing.
				FlowStatement::DeclareContinuation { body, .. } => body.apply(substitution),
			}
		}

		match &mut self.terminator {
			FlowTerminator::Branch { scrutinee, .. } => scrutinee.apply(substitution),
			FlowTerminator::Apply {
				procedure,
				snapshot,
				argument,
				..
			} => [procedure, snapshot, argument].map(|x| x.apply(substitution)).ignore(),
			FlowTerminator::Jump { argument, .. } => argument.apply(substitution),
		}
	}
}

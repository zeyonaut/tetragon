use std::{collections::HashMap, hash::Hash};

use super::cypress::CypressVariable;
use crate::{
	translator::label::{Label, LabelGenerator},
	utility::slice::{slice, Slice},
};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum FireflyProjector {
	Parameter,
	Field(usize),
	Free(usize),
	Dereference,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct FireflyProjection {
	pub root: CypressVariable,
	pub projectors: Vec<FireflyProjector>,
}

impl FireflyProjection {
	pub fn new(root: CypressVariable) -> Self {
		Self {
			root,
			projectors: Vec::new(),
		}
	}

	pub fn project(mut self, projector: FireflyProjector) -> Self {
		self.projectors.push(projector);
		self
	}

	pub fn is_indirect(&self) -> bool {
		for projector in &self.projectors {
			if matches!(projector, FireflyProjector::Field(_) | FireflyProjector::Dereference) {
				return true;
			}
		}
		false
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyOperand {
	Copy(FireflyProjection),
	Constant(FireflyPrimitive),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FireflyType {
	Unity,
	Polarity,
	Integer,
	Product(Slice<Self>),
	Procedure,
	Snapshot(Option<Slice<Self>>),
}

pub fn ff_closure_type() -> FireflyType {
	FireflyType::Product(slice![FireflyType::Procedure, FireflyType::Snapshot(None),])
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyValue {
	Unity,
	Polarity(bool),
	Integer(i64),
	Procedure(Label),
	Tuple(Slice<Self>),
	Snapshot(Slice<Self>),
	Address(FireflyProjection),
}

// Primitives are essentially nullary operations that can't fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyPrimitive {
	Unity,
	Polarity(bool),
	Integer(i64),
	Procedure(Label),
}

impl FireflyPrimitive {
	fn evaluate(&self) -> FireflyValue {
		match self {
			Self::Unity => FireflyValue::Unity,
			Self::Polarity(x) => FireflyValue::Polarity(*x),
			Self::Integer(x) => FireflyValue::Integer(*x),
			Self::Procedure(x) => FireflyValue::Procedure(*x),
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryOperator {
	EqualsQuery(FireflyType),
	Add,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyOperation {
	Address(FireflyProjection),
	Id(FireflyType, FireflyOperand),
	Binary(BinaryOperator, [FireflyOperand; 2]),
	Pair(Slice<(FireflyType, FireflyOperand)>),
	Closure(FireflyOperand, Slice<(FireflyType, FireflyOperand)>),
}

impl FireflyOperation {
	fn evaluate(
		&self,
		intrinsics: &HashMap<String, FireflyValue>,
		variables: &HashMap<Label, FireflyValue>,
	) -> Option<FireflyValue> {
		use FireflyValue::*;
		match self {
			FireflyOperation::Address(projection) => Some(FireflyValue::Address(projection.clone())),
			FireflyOperation::Id(_, operand) => compute(intrinsics, variables, operand),
			FireflyOperation::Binary(operator, [x, y]) => match operator {
				BinaryOperator::EqualsQuery(_) => Some(Polarity(
					compute(intrinsics, variables, x)? == compute(intrinsics, variables, y)?,
				)),
				BinaryOperator::Add => {
					if let (Some(Integer(x)), Some(Integer(y))) =
						(compute(intrinsics, variables, x), compute(intrinsics, variables, y))
					{
						Some(Integer(x + y))
					} else {
						None
					}
				},
			},
			FireflyOperation::Pair(parts) => Some(Tuple(
				parts
					.iter()
					.map(|(_, operand)| compute(intrinsics, variables, operand))
					.collect::<Option<Vec<_>>>()?
					.into_boxed_slice(),
			)),
			FireflyOperation::Closure(procedure, snapshot_operands) => {
				let procedure = compute(intrinsics, variables, procedure)?;
				let snapshot_operands = snapshot_operands
					.into_iter()
					.map(|(_, operand)| Some(compute(intrinsics, variables, operand)?))
					.collect::<Option<Vec<_>>>()?
					.into_boxed_slice();

				Some(FireflyValue::Tuple(slice![
					procedure,
					FireflyValue::Snapshot(snapshot_operands)
				]))
			},
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyStatement {
	Assign {
		binding: Label,
		operation: FireflyOperation,
	},
	DeclareContinuation {
		label: Label,
		parameter: Label,
		domain: FireflyType,
		body: FireflyTerm,
	},
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyTerminator {
	Branch {
		scrutinee: FireflyOperand,
		yes_continuation: Label,
		no_continuation: Label,
	},
	Apply {
		procedure: FireflyOperand,
		domain: FireflyType,
		codomain: FireflyType,
		snapshot: FireflyOperand,
		continuation_label: Option<Label>,
		argument: FireflyOperand,
	},
	Jump {
		continuation_label: Option<Label>,
		domain: FireflyType,
		argument: FireflyOperand,
	},
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FireflyTerm {
	pub statements: Vec<FireflyStatement>,
	pub terminator: FireflyTerminator,
}

impl FireflyTerm {
	pub fn new(terminator: FireflyTerminator) -> Self {
		Self {
			statements: Vec::new(),
			terminator,
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FireflyProcedure {
	pub capture: Option<(Label, Slice<FireflyType>)>,
	// TODO: Add type of environment. (a slice of types would be most convenient)
	pub parameter: Option<Label>,
	pub domain: FireflyType,
	pub body: FireflyTerm,
	pub codomain: FireflyType,
	// TODO: Add codomain.
}

#[derive(Clone, Debug)]
struct FireflyContinuation<'a> {
	parameter: Label,
	body: &'a FireflyTerm,
}

#[derive(Debug, Clone)]
pub struct FireflyProgram {
	pub procedures: HashMap<Label, FireflyProcedure>,
	pub entry: Label,
	pub symbol_generator: LabelGenerator,
}

impl FireflyProgram {
	pub fn evaluate(mut self) -> Option<FireflyValue> {
		let intrinsics = self.insert_intrinsics();
		let mut term = &self.procedures.get(&self.entry)?.body;
		let mut return_stack = Vec::<(Label, HashMap<Label, FireflyValue>)>::new();
		let mut continuations: HashMap<Label, FireflyContinuation> = HashMap::new();
		let mut environment = HashMap::<Label, FireflyValue>::new();
		loop {
			for statement in &term.statements {
				match statement {
					FireflyStatement::Assign { binding, operation } => {
						environment.insert(binding.clone(), operation.evaluate(&intrinsics, &environment)?);
					},
					FireflyStatement::DeclareContinuation {
						label,
						parameter,
						domain: _,
						body,
					} => {
						continuations.entry(label.clone()).or_insert_with(|| FireflyContinuation {
							parameter: parameter.clone(),
							body,
						});
					},
				}
			}

			term = match &term.terminator {
				FireflyTerminator::Branch {
					scrutinee,
					yes_continuation,
					no_continuation,
				} => {
					if let FireflyValue::Polarity(scrutinee) = compute(&intrinsics, &environment, scrutinee)? {
						let continuation_label = if scrutinee { yes_continuation } else { no_continuation };

						let continuation = continuations.get(&continuation_label)?;

						continuation.body
					} else {
						return None;
					}
				},
				FireflyTerminator::Apply {
					procedure,
					domain: _,
					codomain: _,
					snapshot,
					continuation_label,
					argument,
				} => {
					let procedure = compute(&intrinsics, &environment, procedure)?;
					let snapshot = compute(&intrinsics, &environment, snapshot)?;
					if let FireflyValue::Procedure(procedure_label) = procedure {
						let procedure = self.procedures.get(&procedure_label)?;

						if let Some(continuation_label) = continuation_label {
							return_stack.push((continuation_label.clone(), environment.clone()));
						}

						let argument = compute(&intrinsics, &environment, argument)?;

						environment = HashMap::new();
						if let Some((shadow, _)) = procedure.capture {
							environment.insert(shadow, snapshot);
						}
						if let Some(parameter) = procedure.parameter {
							environment.insert(parameter, argument);
						}

						&procedure.body
					} else {
						return None;
					}
				},
				FireflyTerminator::Jump {
					continuation_label,
					domain: _,
					argument,
				} => {
					if let Some(label) = continuation_label {
						let continuation = continuations.get(&label).cloned()?;
						environment.insert(continuation.parameter, compute(&intrinsics, &environment, argument)?);
						continuation.body
					} else if let Some((returner_label, mut returner_environment)) = return_stack.pop() {
						let continuation = continuations.get(&returner_label).cloned()?;
						returner_environment.insert(continuation.parameter, compute(&intrinsics, &environment, argument)?);
						environment = returner_environment;
						continuation.body
					} else {
						return compute(&intrinsics, &environment, argument);
					}
				},
			}
		}
	}

	fn insert_intrinsics(&mut self) -> HashMap<String, FireflyValue> {
		let mut intrinsics = HashMap::new();

		{
			let [left_inner] = [0].map(FireflyProjector::Free);
			let [add_inner] = self.symbol_generator.fresh();
			{
				let [environment, right, output] = self.symbol_generator.fresh();
				self.procedures.insert(
					add_inner,
					FireflyProcedure {
						capture: Some((environment, slice![FireflyType::Integer])),
						parameter: Some(right),
						domain: FireflyType::Integer,
						codomain: FireflyType::Integer,
						body: FireflyTerm {
							statements: vec![FireflyStatement::Assign {
								binding: output,
								operation: FireflyOperation::Binary(
									BinaryOperator::Add,
									[
										FireflyOperand::Copy(
											FireflyProjection::new(CypressVariable::Local(environment)).project(left_inner),
										),
										FireflyOperand::Copy(
											FireflyProjection::new(CypressVariable::Local(right))
												.project(FireflyProjector::Parameter),
										),
									],
								),
							}],
							terminator: FireflyTerminator::Jump {
								continuation_label: None,
								domain: FireflyType::Integer,
								argument: FireflyOperand::Copy(FireflyProjection::new(CypressVariable::Local(output))),
							},
						},
					},
				);
			}

			let [add, left, add_inner_closure] = self.symbol_generator.fresh();
			self.procedures.insert(
				add,
				FireflyProcedure {
					capture: None,
					parameter: Some(left),
					domain: FireflyType::Integer,
					codomain: ff_closure_type(),
					body: FireflyTerm {
						statements: vec![FireflyStatement::Assign {
							binding: add_inner_closure,
							operation: FireflyOperation::Closure(
								FireflyOperand::Constant(FireflyPrimitive::Procedure(add_inner)),
								slice![(
									FireflyType::Integer,
									FireflyOperand::Copy(
										FireflyProjection::new(CypressVariable::Local(left))
											.project(FireflyProjector::Parameter)
									)
								)],
							),
						}],
						terminator: FireflyTerminator::Jump {
							continuation_label: None,
							domain: ff_closure_type(),
							argument: FireflyOperand::Copy(FireflyProjection::new(CypressVariable::Local(add_inner_closure))),
						},
					},
				},
			);

			intrinsics.insert(
				"add".to_owned(),
				FireflyValue::Tuple(slice![FireflyValue::Procedure(add), FireflyValue::Snapshot(slice![])]),
			);
		}

		{
			let [add2, input, output] = self.symbol_generator.fresh();
			self.procedures.insert(
				add2,
				FireflyProcedure {
					capture: None,
					parameter: Some(input),
					domain: FireflyType::Product(slice![FireflyType::Integer, FireflyType::Integer]),
					codomain: FireflyType::Integer,
					body: FireflyTerm {
						statements: vec![FireflyStatement::Assign {
							binding: output,
							operation: FireflyOperation::Binary(
								BinaryOperator::Add,
								[
									FireflyOperand::Copy(
										FireflyProjection::new(CypressVariable::Local(input))
											.project(FireflyProjector::Parameter)
											.project(FireflyProjector::Field(0)),
									),
									FireflyOperand::Copy(
										FireflyProjection::new(CypressVariable::Local(input))
											.project(FireflyProjector::Parameter)
											.project(FireflyProjector::Field(1)),
									),
								],
							),
						}],
						terminator: FireflyTerminator::Jump {
							continuation_label: None,
							domain: FireflyType::Integer,
							argument: FireflyOperand::Copy(FireflyProjection::new(CypressVariable::Local(output))),
						},
					},
				},
			);
			intrinsics.insert(
				"add2".to_owned(),
				FireflyValue::Tuple(slice![FireflyValue::Procedure(add2), FireflyValue::Snapshot(slice![])]),
			);
		}

		intrinsics
	}
}

fn lookup(
	intrinsics: &HashMap<String, FireflyValue>,
	environment: &HashMap<Label, FireflyValue>,
	projection: &FireflyProjection,
) -> Option<FireflyValue> {
	let mut value = match &projection.root {
		CypressVariable::Local(local) => environment.get(local)?.clone(),
		CypressVariable::Global(global) => intrinsics.get(global)?.clone(),
	};

	for projector in &projection.projectors {
		match projector {
			FireflyProjector::Parameter => {
				continue;
			},
			FireflyProjector::Field(index) => {
				value = if let FireflyValue::Tuple(parts) = value {
					parts.get(*index)?.clone()
				} else {
					return None;
				}
			},
			FireflyProjector::Free(index) => {
				value = if let FireflyValue::Snapshot(parts) = value {
					parts.get(*index)?.clone()
				} else {
					return None;
				}
			},
			FireflyProjector::Dereference => {
				value = if let FireflyValue::Address(projection) = value {
					lookup(intrinsics, environment, &projection)?
				} else {
					return None;
				}
			},
		};
	}

	Some(value)
}

fn compute(
	intrinsics: &HashMap<String, FireflyValue>,
	environment: &HashMap<Label, FireflyValue>,
	operand: &FireflyOperand,
) -> Option<FireflyValue> {
	match operand {
		FireflyOperand::Copy(projection) => lookup(intrinsics, environment, &projection),
		FireflyOperand::Constant(primitive) => Some(primitive.evaluate()),
	}
}

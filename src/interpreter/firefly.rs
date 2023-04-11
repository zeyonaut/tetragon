use std::hash::Hash;

use halfbrown::HashMap;

use super::cypress::CypressVariable;
use crate::{
	translator::label::{Label, LabelGenerator},
	utility::slice::{slice, Slice},
};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum FireflyProjector {
	Field(usize),
	Free(usize),
	Procedure,
	Snapshot,
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyOperand {
	Copy(FireflyProjection),
	Constant(FireflyPrimitive),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FireflyType {
	Unity,
	Polarity,
	Integer,
	Product(Slice<Self>),
	Procedure,
	Snapshot(Slice<Self>),
	Closure,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyValue {
	Unity,
	Polarity(bool),
	Integer(i64),
	Procedure(Label),
	Tuple(Slice<Self>),
	Snapshot(Slice<Self>),
	Closure(Box<Self>, Slice<Self>),
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
	EqualsQuery,
	Add,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyOperation {
	Id(FireflyType, FireflyOperand),
	Binary(BinaryOperator, [FireflyOperand; 2]),
	Pair(Slice<(FireflyType, FireflyOperand)>),
	Closure(FireflyOperand, Slice<FireflyOperand>),
}

impl FireflyOperation {
	fn evaluate(
		&self,
		intrinsics: &HashMap<String, FireflyValue>,
		variables: &HashMap<Label, FireflyValue>,
	) -> Option<FireflyValue> {
		use FireflyValue::*;
		match self {
			FireflyOperation::Id(ty, operand) => compute(intrinsics, variables, operand),
			FireflyOperation::Binary(operator, [x, y]) => match operator {
				BinaryOperator::EqualsQuery => Some(Polarity(
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
					.map(|(ty, operand)| compute(intrinsics, variables, operand))
					.collect::<Option<Vec<_>>>()?
					.into_boxed_slice(),
			)),
			FireflyOperation::Closure(procedure, snapshot_operands) => {
				let procedure = compute(intrinsics, variables, procedure)?;
				let snapshot_operands = snapshot_operands
					.into_iter()
					.map(|operand| Some(compute(intrinsics, variables, operand)?))
					.collect::<Option<Vec<_>>>()?
					.into_boxed_slice();

				Some(FireflyValue::Closure(Box::new(procedure), snapshot_operands))
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
		snapshot: FireflyOperand,
		continuation_label: Option<Label>,
		argument: FireflyOperand,
	},
	Jump {
		continuation_label: Option<Label>,
		argument: FireflyOperand,
	},
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FireflyTerm {
	// Stored as a stack: the last statement is the first to execute.
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
	pub environment: Option<Label>,
	// TODO: Add type of environment. (a slice of types would be most convenient)
	pub parameter: Option<Label>,
	// TODO: Add domain.
	pub body: FireflyTerm,
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
			for statement in term.statements.iter().rev() {
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
						if let Some(shadow) = procedure.environment {
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
						environment: Some(environment),
						parameter: Some(right),
						body: FireflyTerm {
							statements: vec![FireflyStatement::Assign {
								binding: output,
								operation: FireflyOperation::Binary(
									BinaryOperator::Add,
									[
										FireflyOperand::Copy(
											FireflyProjection::new(CypressVariable::Local(environment)).project(left_inner),
										),
										FireflyOperand::Copy(FireflyProjection::new(CypressVariable::Local(right))),
									],
								),
							}],
							terminator: FireflyTerminator::Jump {
								continuation_label: None,
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
					environment: None,
					parameter: Some(left),
					body: FireflyTerm {
						statements: vec![FireflyStatement::Assign {
							binding: add_inner_closure,
							operation: FireflyOperation::Closure(
								FireflyOperand::Constant(FireflyPrimitive::Procedure(add_inner)),
								slice![FireflyOperand::Copy(FireflyProjection::new(CypressVariable::Local(left)))],
							),
						}],
						terminator: FireflyTerminator::Jump {
							continuation_label: None,
							argument: FireflyOperand::Copy(FireflyProjection::new(CypressVariable::Local(add_inner_closure))),
						},
					},
				},
			);

			intrinsics.insert(
				"add".to_owned(),
				FireflyValue::Closure(Box::new(FireflyValue::Procedure(add)), slice![]),
			);
		}

		{
			let [add2, input, output] = self.symbol_generator.fresh();
			self.procedures.insert(
				add2,
				FireflyProcedure {
					environment: None,
					parameter: Some(input),
					body: FireflyTerm {
						statements: vec![FireflyStatement::Assign {
							binding: output,
							operation: FireflyOperation::Binary(
								BinaryOperator::Add,
								[
									FireflyOperand::Copy(
										FireflyProjection::new(CypressVariable::Local(input))
											.project(FireflyProjector::Field(0)),
									),
									FireflyOperand::Copy(
										FireflyProjection::new(CypressVariable::Local(input))
											.project(FireflyProjector::Field(1)),
									),
								],
							),
						}],
						terminator: FireflyTerminator::Jump {
							continuation_label: None,
							argument: FireflyOperand::Copy(FireflyProjection::new(CypressVariable::Local(output))),
						},
					},
				},
			);
			intrinsics.insert(
				"add2".to_owned(),
				FireflyValue::Closure(Box::new(FireflyValue::Procedure(add2)), slice![]),
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
			FireflyProjector::Procedure => {
				value = if let FireflyValue::Closure(procedure_label, _) = value {
					if let FireflyValue::Procedure(procedure_label) = *procedure_label {
						FireflyValue::Procedure(procedure_label)
					} else {
						return None;
					}
				} else {
					return None;
				}
			},
			FireflyProjector::Snapshot => {
				value = if let FireflyValue::Closure(_, snapshot) = value {
					FireflyValue::Snapshot(snapshot)
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

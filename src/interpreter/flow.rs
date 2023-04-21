use std::{collections::HashMap, hash::Hash};

use crate::{
	translator::label::{Label, LabelGenerator},
	utility::slice::{slice, Slice},
};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum FlowVariable {
	Local(Label),
	Global(String),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum FlowProjector {
	Parameter,
	Field(usize),
	Free(usize),
	Dereference,
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct FlowProjection {
	pub root: FlowVariable,
	pub projectors: Vec<FlowProjector>,
}

impl FlowProjection {
	pub fn new(root: FlowVariable) -> Self {
		Self {
			root,
			projectors: Vec::new(),
		}
	}

	pub fn project(mut self, projector: FlowProjector) -> Self {
		self.projectors.push(projector);
		self
	}

	pub fn is_indirect(&self) -> bool {
		for projector in &self.projectors {
			if matches!(projector, FlowProjector::Field(_) | FlowProjector::Dereference) {
				return true;
			}
		}
		false
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FlowOperand {
	Copy(FlowProjection),
	Constant(FlowPrimitive),
}

impl FlowOperand {
	pub fn project(mut self, projector: FlowProjector) -> Self {
		match &mut self {
			FlowOperand::Copy(projection) => {
				projection.projectors.push(projector);
			},
			FlowOperand::Constant(_) => panic!("can't project from a constant"),
		}
		self
	}
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FlowType {
	Unity,
	Polarity,
	Integer,
	Product(Slice<Self>),
	Procedure,
	Snapshot(Option<Slice<Self>>),
}

pub fn ff_closure_type() -> FlowType {
	FlowType::Product(slice![FlowType::Procedure, FlowType::Snapshot(None),])
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FlowValue {
	Unity,
	Polarity(bool),
	Integer(i64),
	Procedure(Label),
	Tuple(Slice<Self>),
	Snapshot(Slice<Self>),
	Address(FlowProjection),
}

// Primitives are essentially nullary operations that can't fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FlowPrimitive {
	Unity,
	Polarity(bool),
	Integer(i64),
	Procedure(Label),
}

impl FlowPrimitive {
	fn evaluate(&self) -> FlowValue {
		match self {
			Self::Unity => FlowValue::Unity,
			Self::Polarity(x) => FlowValue::Polarity(*x),
			Self::Integer(x) => FlowValue::Integer(*x),
			Self::Procedure(x) => FlowValue::Procedure(*x),
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryOperator {
	EqualsQuery(FlowType),
	Add,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FlowOperation {
	Id(FlowType, FlowOperand),
	Binary(BinaryOperator, [FlowOperand; 2]),
	Pair(Slice<(FlowType, FlowOperand)>),
	Closure(FlowOperand, Slice<(FlowType, FlowOperand)>),
}

impl FlowOperation {
	fn evaluate(&self, intrinsics: &HashMap<String, FlowValue>, variables: &HashMap<Label, FlowValue>) -> Option<FlowValue> {
		use FlowValue::*;
		match self {
			FlowOperation::Id(_, operand) => compute(intrinsics, variables, operand),
			FlowOperation::Binary(operator, [x, y]) => match operator {
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
			FlowOperation::Pair(parts) => Some(Tuple(
				parts
					.iter()
					.map(|(_, operand)| compute(intrinsics, variables, operand))
					.collect::<Option<Vec<_>>>()?
					.into_boxed_slice(),
			)),
			FlowOperation::Closure(procedure, snapshot_operands) => {
				let procedure = compute(intrinsics, variables, procedure)?;
				let snapshot_operands = snapshot_operands
					.into_iter()
					.map(|(_, operand)| Some(compute(intrinsics, variables, operand)?))
					.collect::<Option<Vec<_>>>()?
					.into_boxed_slice();

				Some(FlowValue::Tuple(slice![procedure, FlowValue::Snapshot(snapshot_operands)]))
			},
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FlowStatement {
	Assign {
		binding: Label,
		operation: FlowOperation,
	},
	DeclareContinuation {
		label: Label,
		parameter: Label,
		domain: FlowType,
		body: FlowTerm,
	},
}

impl FlowStatement {
	pub fn prepend_to(self, mut term: FlowTerm) -> FlowTerm {
		term.statements.insert(0, self);
		term
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FlowTerminator {
	Branch {
		scrutinee: FlowOperand,
		yes_continuation: Label,
		no_continuation: Label,
	},
	Apply {
		procedure: FlowOperand,
		domain: FlowType,
		codomain: FlowType,
		snapshot: FlowOperand,
		continuation_label: Option<Label>,
		argument: FlowOperand,
	},
	Jump {
		continuation_label: Option<Label>,
		domain: FlowType,
		argument: FlowOperand,
	},
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlowTerm {
	pub statements: Vec<FlowStatement>,
	pub terminator: FlowTerminator,
}

impl FlowTerm {
	pub fn new(terminator: FlowTerminator) -> Self {
		Self {
			statements: Vec::new(),
			terminator,
		}
	}

	pub fn compose(mut statements: Vec<FlowStatement>, mut term: Self) -> Self {
		Self {
			statements: {
				statements.append(&mut term.statements);
				statements
			},
			terminator: term.terminator,
		}
	}
}

impl From<FlowTerminator> for FlowTerm {
	fn from(value: FlowTerminator) -> Self {
		Self {
			statements: vec![],
			terminator: value,
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlowProcedure {
	pub capture: Option<(Label, Slice<FlowType>)>,
	pub parameter: Option<Label>,
	pub domain: FlowType,
	pub body: FlowTerm,
	pub codomain: FlowType,
}

#[derive(Clone, Debug)]
struct FlowContinuation<'a> {
	parameter: Label,
	body: &'a FlowTerm,
}

#[derive(Debug, Clone)]
pub struct FlowProgram {
	pub procedures: HashMap<Label, FlowProcedure>,
	pub entry: Label,
	pub symbol_generator: LabelGenerator,
}

impl FlowProgram {
	pub fn evaluate(mut self) -> Option<FlowValue> {
		let intrinsics = self.insert_intrinsics();
		let mut term = &self.procedures.get(&self.entry)?.body;
		let mut return_stack = Vec::<(Label, HashMap<Label, FlowValue>)>::new();
		let mut continuations: HashMap<Label, FlowContinuation> = HashMap::new();
		let mut environment = HashMap::<Label, FlowValue>::new();
		loop {
			for statement in &term.statements {
				match statement {
					FlowStatement::Assign { binding, operation } => {
						environment.insert(binding.clone(), operation.evaluate(&intrinsics, &environment)?);
					},
					FlowStatement::DeclareContinuation {
						label,
						parameter,
						domain: _,
						body,
					} => {
						continuations.entry(label.clone()).or_insert_with(|| FlowContinuation {
							parameter: parameter.clone(),
							body,
						});
					},
				}
			}

			term = match &term.terminator {
				FlowTerminator::Branch {
					scrutinee,
					yes_continuation,
					no_continuation,
				} => {
					if let FlowValue::Polarity(scrutinee) = compute(&intrinsics, &environment, scrutinee)? {
						let continuation_label = if scrutinee { yes_continuation } else { no_continuation };

						let continuation = continuations.get(&continuation_label)?;

						continuation.body
					} else {
						return None;
					}
				},
				FlowTerminator::Apply {
					procedure,
					domain: _,
					codomain: _,
					snapshot,
					continuation_label,
					argument,
				} => {
					let procedure = compute(&intrinsics, &environment, procedure)?;
					let snapshot = compute(&intrinsics, &environment, snapshot)?;
					if let FlowValue::Procedure(procedure_label) = procedure {
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
				FlowTerminator::Jump {
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

	fn insert_intrinsics(&mut self) -> HashMap<String, FlowValue> {
		let mut intrinsics = HashMap::new();

		{
			let [left_inner] = [0].map(FlowProjector::Free);
			let [add_inner] = self.symbol_generator.fresh();
			{
				let [environment, right, output] = self.symbol_generator.fresh();
				self.procedures.insert(
					add_inner,
					FlowProcedure {
						capture: Some((environment, slice![FlowType::Integer])),
						parameter: Some(right),
						domain: FlowType::Integer,
						codomain: FlowType::Integer,
						body: FlowTerm {
							statements: vec![FlowStatement::Assign {
								binding: output,
								operation: FlowOperation::Binary(
									BinaryOperator::Add,
									[
										FlowOperand::Copy(
											FlowProjection::new(FlowVariable::Local(environment)).project(left_inner),
										),
										FlowOperand::Copy(
											FlowProjection::new(FlowVariable::Local(right)).project(FlowProjector::Parameter),
										),
									],
								),
							}],
							terminator: FlowTerminator::Jump {
								continuation_label: None,
								domain: FlowType::Integer,
								argument: FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(output))),
							},
						},
					},
				);
			}

			let [add, left, add_inner_closure] = self.symbol_generator.fresh();
			self.procedures.insert(
				add,
				FlowProcedure {
					capture: None,
					parameter: Some(left),
					domain: FlowType::Integer,
					codomain: ff_closure_type(),
					body: FlowTerm {
						statements: vec![FlowStatement::Assign {
							binding: add_inner_closure,
							operation: FlowOperation::Closure(
								FlowOperand::Constant(FlowPrimitive::Procedure(add_inner)),
								slice![(
									FlowType::Integer,
									FlowOperand::Copy(
										FlowProjection::new(FlowVariable::Local(left)).project(FlowProjector::Parameter)
									)
								)],
							),
						}],
						terminator: FlowTerminator::Jump {
							continuation_label: None,
							domain: ff_closure_type(),
							argument: FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(add_inner_closure))),
						},
					},
				},
			);

			intrinsics.insert(
				"add".to_owned(),
				FlowValue::Tuple(slice![FlowValue::Procedure(add), FlowValue::Snapshot(slice![])]),
			);
		}

		{
			let [add2, input, output] = self.symbol_generator.fresh();
			self.procedures.insert(
				add2,
				FlowProcedure {
					capture: None,
					parameter: Some(input),
					domain: FlowType::Product(slice![FlowType::Integer, FlowType::Integer]),
					codomain: FlowType::Integer,
					body: FlowTerm {
						statements: vec![FlowStatement::Assign {
							binding: output,
							operation: FlowOperation::Binary(
								BinaryOperator::Add,
								[
									FlowOperand::Copy(
										FlowProjection::new(FlowVariable::Local(input))
											.project(FlowProjector::Parameter)
											.project(FlowProjector::Field(0)),
									),
									FlowOperand::Copy(
										FlowProjection::new(FlowVariable::Local(input))
											.project(FlowProjector::Parameter)
											.project(FlowProjector::Field(1)),
									),
								],
							),
						}],
						terminator: FlowTerminator::Jump {
							continuation_label: None,
							domain: FlowType::Integer,
							argument: FlowOperand::Copy(FlowProjection::new(FlowVariable::Local(output))),
						},
					},
				},
			);
			intrinsics.insert(
				"add2".to_owned(),
				FlowValue::Tuple(slice![FlowValue::Procedure(add2), FlowValue::Snapshot(slice![])]),
			);
		}

		intrinsics
	}
}

fn lookup(
	intrinsics: &HashMap<String, FlowValue>,
	environment: &HashMap<Label, FlowValue>,
	projection: &FlowProjection,
) -> Option<FlowValue> {
	let mut value = match &projection.root {
		FlowVariable::Local(local) => environment.get(local)?.clone(),
		FlowVariable::Global(global) => intrinsics.get(global)?.clone(),
	};

	for projector in &projection.projectors {
		match projector {
			FlowProjector::Parameter => {
				continue;
			},
			FlowProjector::Field(index) => {
				value = if let FlowValue::Tuple(parts) = value {
					parts.get(*index)?.clone()
				} else {
					return None;
				}
			},
			FlowProjector::Free(index) => {
				value = if let FlowValue::Snapshot(parts) = value {
					parts.get(*index)?.clone()
				} else {
					return None;
				}
			},
			FlowProjector::Dereference => {
				value = if let FlowValue::Address(projection) = value {
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
	intrinsics: &HashMap<String, FlowValue>,
	environment: &HashMap<Label, FlowValue>,
	operand: &FlowOperand,
) -> Option<FlowValue> {
	match operand {
		FlowOperand::Copy(projection) => lookup(intrinsics, environment, &projection),
		FlowOperand::Constant(primitive) => Some(primitive.evaluate()),
	}
}

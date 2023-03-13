use std::{collections::HashSet, hash::Hash, sync::Arc};

use halfbrown::HashMap;

use crate::{
	translator::label::{Label, LabelGenerator},
	utility::slice::Slice,
};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum FireflyVariable {
	Local(Label),
	Global(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FireflyType {
	Unity,
	Polarity,
	Integer,
	Power { domain: Box<Self>, codomain: Box<Self> },
	Product(Vec<Self>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyValue {
	Unity,
	Polarity(bool),
	Integer(i64),
	Tuple(Vec<Self>),
	Closure(Label, HashMap<Label, Self>),
}

// Primitives are essentially nullary operations that can't fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyPrimitive {
	Unity,
	Polarity(bool),
	Integer(i64),
}

// TODO: Factor out duplicated code across CPS representations.
impl FireflyPrimitive {
	fn evaluate(&self) -> FireflyValue {
		match self {
			Self::Unity => FireflyValue::Unity,
			Self::Polarity(x) => FireflyValue::Polarity(*x),
			Self::Integer(x) => FireflyValue::Integer(*x),
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyOperation {
	EqualsQuery([FireflyVariable; 2]),
	Projection(FireflyVariable, usize),
	Add([FireflyVariable; 2]),
	Pair(Slice<FireflyVariable>),
}

// TODO: Factor out duplicated code across CPS representations.
impl FireflyOperation {
	fn evaluate(
		&self,
		intrinsics: &HashMap<String, FireflyValue>,
		variables: &HashMap<Label, FireflyValue>,
	) -> Option<FireflyValue> {
		use FireflyValue::*;
		match self {
			FireflyOperation::EqualsQuery([x, y]) => Some(Polarity(
				lookup(intrinsics, variables, &x)? == lookup(intrinsics, variables, &y)?,
			)),
			FireflyOperation::Projection(tuple, index) => {
				if let Tuple(parts) = lookup(intrinsics, variables, &tuple)? {
					parts.get(*index).cloned()
				} else {
					None
				}
			},
			FireflyOperation::Add([x, y]) => {
				if let (Some(Integer(x)), Some(Integer(y))) =
					(lookup(intrinsics, variables, &x), lookup(intrinsics, variables, &y))
				{
					Some(Integer(x + y))
				} else {
					None
				}
			},
			FireflyOperation::Pair(parts) => Some(Tuple(
				parts
					.as_ref()
					.into_iter()
					.map(|variable| lookup(intrinsics, variables, &variable))
					.collect::<Option<Vec<_>>>()?,
			)),
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyStatement {
	AssignPrimitive {
		binding: Label,
		value: FireflyPrimitive,
	},
	AssignOperation {
		binding: Label,
		operation: FireflyOperation,
	},
	AssignClosure {
		binding: Label,
		procedure: Label,
		environment_parameters_to_arguments: HashMap<Label, Label>,
	},
	DeclareContinuation {
		label: Label,
		parameter: Label,
		body: FireflyTerm,
	},
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyTerminator {
	Branch {
		scrutinee: FireflyVariable,
		yes_continuation: Label,
		no_continuation: Label,
	},
	Apply {
		closure: FireflyVariable,
		continuation_label: Option<Label>,
		argument: FireflyVariable,
	},
	Jump {
		continuation_label: Option<Label>,
		argument: FireflyVariable,
	},
	Halt {
		argument: FireflyVariable,
	},
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FireflyTerm {
	// Stored as a stack: the last statement is the first.
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
	pub fixpoint_variable: Option<Label>,
	pub environment_parameters: HashSet<Label>,
	pub parameter: Label,
	pub body: FireflyTerm,
}

#[derive(Clone, Debug)]
struct FireflyContinuation<'a> {
	parameter: Label,
	body: &'a FireflyTerm,
}

#[derive(Debug)]
pub struct FireflyProgram {
	pub procedures: HashMap<Label, FireflyProcedure>,
	pub entry: FireflyTerm,
	pub symbol_generator: LabelGenerator,
}

impl FireflyProgram {
	pub fn evaluate(mut self) -> Option<FireflyValue> {
		let mut intrinsics = self.insert_intrinsics();
		let mut term = &self.entry;
		let mut return_stack = Vec::<(Label, HashMap<Label, FireflyValue>)>::new();
		let mut continuations: HashMap<Label, FireflyContinuation> = HashMap::new();
		let mut environment = HashMap::<Label, FireflyValue>::new();
		loop {
			for statement in term.statements.iter().rev() {
				match statement {
					FireflyStatement::AssignPrimitive { binding, value } => {
						environment.insert(binding.clone(), value.evaluate());
					},
					FireflyStatement::AssignOperation { binding, operation } => {
						environment.insert(binding.clone(), operation.evaluate(&intrinsics, &environment)?);
					},
					FireflyStatement::AssignClosure {
						binding,
						procedure,
						environment_parameters_to_arguments,
					} => {
						let environment_parameters_to_arguments = environment_parameters_to_arguments
							.into_iter()
							.map(|(k, v)| Some((k.clone(), environment.get(&v).cloned()?)))
							.collect::<Option<HashMap<_, _>>>()?;
						environment.insert(
							binding.clone(),
							FireflyValue::Closure(procedure.clone(), environment_parameters_to_arguments),
						);
					},
					FireflyStatement::DeclareContinuation { label, parameter, body } => {
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
					if let FireflyValue::Polarity(scrutinee) = lookup(&intrinsics, &environment, &scrutinee)? {
						let continuation_label = if scrutinee { yes_continuation } else { no_continuation };

						let continuation = continuations.get(&continuation_label)?;

						continuation.body
					} else {
						return None;
					}
				},
				FireflyTerminator::Apply {
					closure,
					continuation_label,
					argument,
				} => {
					let closure = lookup(&intrinsics, &environment, &closure)?;
					if let FireflyValue::Closure(procedure_label, environment_parameters_to_arguments) = closure {
						let procedure = self.procedures.get(&procedure_label)?;

						if let Some(continuation_label) = continuation_label {
							return_stack.push((continuation_label.clone(), environment.clone()));
						}

						let argument = lookup(&intrinsics, &environment, &argument)?;
						environment = environment_parameters_to_arguments;
						environment.insert(procedure.parameter, argument);

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
						environment.insert(continuation.parameter, lookup(&intrinsics, &environment, &argument)?);
						continuation.body
					} else if let Some((returner_label, mut returner_environment)) = return_stack.pop() {
						let continuation = continuations.get(&returner_label).cloned()?;
						returner_environment.insert(continuation.parameter, lookup(&intrinsics, &environment, &argument)?);
						environment = returner_environment;
						continuation.body
					} else {
						return lookup(&intrinsics, &environment, &argument);
					}
				},
				FireflyTerminator::Halt { argument } => {
					return match argument {
						FireflyVariable::Local(argument) => environment.remove(argument),
						FireflyVariable::Global(argument) => intrinsics.remove(argument),
					}
				},
			}
		}
	}

	fn insert_intrinsics(&mut self) -> HashMap<String, FireflyValue> {
		let mut intrinsics = HashMap::new();

		{
			let [add_inner, left_inner] = self.symbol_generator.fresh();
			{
				let [right, output] = self.symbol_generator.fresh();
				self.procedures.insert(
					add_inner,
					FireflyProcedure {
						fixpoint_variable: None,
						environment_parameters: HashSet::from([left_inner]),
						parameter: right,
						body: FireflyTerm {
							statements: vec![FireflyStatement::AssignOperation {
								binding: output,
								operation: FireflyOperation::Add([
									FireflyVariable::Local(left_inner),
									FireflyVariable::Local(right),
								]),
							}],
							terminator: FireflyTerminator::Jump {
								continuation_label: None,
								argument: FireflyVariable::Local(output),
							},
						},
					},
				);
			}

			let [add, left, add_inner_closure] = self.symbol_generator.fresh();
			self.procedures.insert(
				add,
				FireflyProcedure {
					fixpoint_variable: None,
					environment_parameters: HashSet::new(),
					parameter: left,
					body: FireflyTerm {
						statements: vec![FireflyStatement::AssignClosure {
							binding: add_inner_closure,
							procedure: add_inner,
							environment_parameters_to_arguments: hashmap![left_inner => left],
						}],
						terminator: FireflyTerminator::Jump {
							continuation_label: None,
							argument: FireflyVariable::Local(add_inner_closure),
						},
					},
				},
			);

			intrinsics.insert("add".to_owned(), FireflyValue::Closure(add, HashMap::new()));
		}

		{
			let [add2, input, left, right, output] = self.symbol_generator.fresh();
			self.procedures.insert(
				add2,
				FireflyProcedure {
					fixpoint_variable: None,
					environment_parameters: HashSet::new(),
					parameter: input,
					body: FireflyTerm {
						statements: vec![
							FireflyStatement::AssignOperation {
								binding: output,
								operation: FireflyOperation::Add([FireflyVariable::Local(left), FireflyVariable::Local(right)]),
							},
							FireflyStatement::AssignOperation {
								binding: right,
								operation: FireflyOperation::Projection(FireflyVariable::Local(input), 1),
							},
							FireflyStatement::AssignOperation {
								binding: left,
								operation: FireflyOperation::Projection(FireflyVariable::Local(input), 0),
							},
						],
						terminator: FireflyTerminator::Jump {
							continuation_label: None,
							argument: FireflyVariable::Local(output),
						},
					},
				},
			);
			intrinsics.insert("add2".to_owned(), FireflyValue::Closure(add2, HashMap::new()));
		}

		intrinsics
	}
}

fn lookup(
	intrinsics: &HashMap<String, FireflyValue>,
	environment: &HashMap<Label, FireflyValue>,
	variable: &FireflyVariable,
) -> Option<FireflyValue> {
	match variable {
		FireflyVariable::Local(local) => environment.get(local).cloned(),
		FireflyVariable::Global(global) => intrinsics.get(global).cloned(),
	}
}

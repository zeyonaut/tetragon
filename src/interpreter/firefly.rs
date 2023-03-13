use std::{
	collections::{HashMap, HashSet},
	hash::Hash,
	sync::Arc,
};

use crate::{translator::symbol::SymbolGenerator, utility::slice::Slice};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum FireflyVariable {
	Local(u64),
	Global(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FireflyProcedureLabel(pub u64);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FireflyContinuationLabel(pub u64);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FireflyBindingLabel(pub u64);

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
	Closure(FireflyProcedureLabel, HashMap<FireflyBindingLabel, Self>),
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
	fn evaluate(self) -> FireflyValue {
		match self {
			Self::Unity => FireflyValue::Unity,
			Self::Polarity(x) => FireflyValue::Polarity(x),
			Self::Integer(x) => FireflyValue::Integer(x),
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
		self,
		intrinsics: &HashMap<String, FireflyValue>,
		variables: &HashMap<FireflyBindingLabel, FireflyValue>,
	) -> Option<FireflyValue> {
		use FireflyValue::*;
		match self {
			FireflyOperation::EqualsQuery([x, y]) => Some(Polarity(
				lookup(intrinsics, variables, &x)? == lookup(intrinsics, variables, &y)?,
			)),
			FireflyOperation::Projection(tuple, index) => {
				if let Tuple(parts) = lookup(intrinsics, variables, &tuple)? {
					parts.get(index).cloned()
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
pub enum FireflyTerm {
	AssignPrimitive {
		binding: FireflyBindingLabel,
		value: FireflyPrimitive,
		rest: Box<Self>,
	},
	AssignOperation {
		binding: FireflyBindingLabel,
		operation: FireflyOperation,
		rest: Box<Self>,
	},
	AssignClosure {
		binding: FireflyBindingLabel,
		procedure: FireflyProcedureLabel,
		environment_parameters_to_arguments: HashMap<FireflyBindingLabel, FireflyBindingLabel>,
		rest: Box<Self>,
	},
	DeclareContinuation {
		label: FireflyContinuationLabel,
		parameter: FireflyBindingLabel,
		body: Box<Self>,
		rest: Box<Self>,
	},
	Branch {
		scrutinee: FireflyVariable,
		yes_continuation: FireflyContinuationLabel,
		no_continuation: FireflyContinuationLabel,
	},
	Apply {
		closure: FireflyVariable,
		continuation_label: Option<FireflyContinuationLabel>,
		argument: FireflyVariable,
	},
	Jump {
		continuation_label: Option<FireflyContinuationLabel>,
		argument: FireflyVariable,
	},
	Halt {
		argument: FireflyVariable,
	},
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FireflyProcedure {
	pub fixpoint_variable: Option<FireflyBindingLabel>,
	pub environment_parameters: HashSet<FireflyBindingLabel>,
	pub parameter: FireflyBindingLabel,
	pub body: FireflyTerm,
}

#[derive(Clone, Debug)]
struct FireflyContinuation {
	parameter: FireflyBindingLabel,
	body: FireflyTerm,
}

#[derive(Debug)]
pub struct FireflyProgram {
	pub procedures: HashMap<FireflyProcedureLabel, FireflyProcedure>,
	pub entry: FireflyTerm,
	pub symbol_generator: SymbolGenerator,
}

impl FireflyProgram {
	pub fn evaluate(mut self) -> Option<FireflyValue> {
		let mut intrinsics = self.insert_intrinsics();
		let mut term = self.entry;
		let mut return_stack = Vec::<(FireflyContinuationLabel, HashMap<FireflyBindingLabel, FireflyValue>)>::new();
		let mut continuations: HashMap<FireflyContinuationLabel, Arc<FireflyContinuation>> = HashMap::new();
		let mut environment = HashMap::<FireflyBindingLabel, FireflyValue>::new();
		loop {
			match term {
				FireflyTerm::AssignPrimitive { binding, value, rest } => {
					environment.insert(binding, value.evaluate());

					term = (*rest).clone();
					continue;
				},
				FireflyTerm::AssignOperation {
					binding,
					operation,
					rest,
				} => {
					environment.insert(binding, operation.evaluate(&intrinsics, &environment)?);

					term = *rest;
					continue;
				},
				FireflyTerm::AssignClosure {
					binding,
					procedure,
					environment_parameters_to_arguments,
					rest,
				} => {
					let environment_parameters_to_arguments = environment_parameters_to_arguments
						.into_iter()
						.map(|(k, v)| Some((k, environment.get(&v).cloned()?)))
						.collect::<Option<HashMap<_, _>>>()?;
					environment.insert(binding, FireflyValue::Closure(procedure, environment_parameters_to_arguments));

					term = (*rest).clone();
					continue;
				},
				FireflyTerm::DeclareContinuation {
					label,
					parameter,
					body,
					rest,
				} => {
					continuations
						.entry(label)
						.or_insert_with(|| Arc::new(FireflyContinuation { parameter, body: *body }));

					term = (*rest).clone();
					continue;
				},
				FireflyTerm::Branch {
					scrutinee,
					yes_continuation,
					no_continuation,
				} => {
					if let FireflyValue::Polarity(scrutinee) = lookup(&intrinsics, &environment, &scrutinee)? {
						let continuation_label = if scrutinee { yes_continuation } else { no_continuation };

						let continuation = continuations.get(&continuation_label)?;

						term = continuation.body.clone();
						continue;
					} else {
						break None;
					}
				},
				FireflyTerm::Apply {
					closure,
					continuation_label,
					argument,
				} => {
					let closure = lookup(&intrinsics, &environment, &closure)?;
					if let FireflyValue::Closure(procedure_label, environment_parameters_to_arguments) = closure {
						let procedure = self.procedures.get(&procedure_label)?;

						if let Some(continuation_label) = continuation_label {
							return_stack.push((continuation_label, environment.clone()));
						}

						let argument = lookup(&intrinsics, &environment, &argument)?;
						environment = environment_parameters_to_arguments;
						environment.insert(procedure.parameter, argument);

						term = procedure.body.clone();
					} else {
						break None;
					}
				},
				FireflyTerm::Jump {
					continuation_label,
					argument,
				} => {
					if let Some(label) = continuation_label {
						let continuation = continuations.get(&label).cloned()?;
						term = continuation.body.clone();
						environment.insert(continuation.parameter, lookup(&intrinsics, &environment, &argument)?);
						continue;
					} else if let Some((returner_label, mut returner_environment)) = return_stack.pop() {
						let continuation = continuations.get(&returner_label).cloned()?;
						term = continuation.body.clone();
						returner_environment.insert(continuation.parameter, lookup(&intrinsics, &environment, &argument)?);
						environment = returner_environment;
						continue;
					} else {
						break lookup(&intrinsics, &environment, &argument);
					};
				},
				FireflyTerm::Halt { argument } => {
					break match argument {
						FireflyVariable::Local(argument) => environment.remove(&FireflyBindingLabel(argument)),
						FireflyVariable::Global(argument) => intrinsics.remove(&argument),
					}
				},
			}
		}
	}

	fn insert_intrinsics(&mut self) -> HashMap<String, FireflyValue> {
		let mut intrinsics = HashMap::new();

		{
			let add_inner = FireflyProcedureLabel(self.symbol_generator.fresh());
			let left_inner = FireflyBindingLabel(self.symbol_generator.fresh());
			{
				let right = FireflyBindingLabel(self.symbol_generator.fresh());
				let output = FireflyBindingLabel(self.symbol_generator.fresh());
				self.procedures.insert(
					add_inner,
					FireflyProcedure {
						fixpoint_variable: None,
						environment_parameters: HashSet::from([left_inner]),
						parameter: right,
						body: FireflyTerm::AssignOperation {
							binding: output,
							operation: FireflyOperation::Add([
								FireflyVariable::Local(left_inner.0),
								FireflyVariable::Local(right.0),
							]),
							rest: Box::new(FireflyTerm::Jump {
								continuation_label: None,
								argument: FireflyVariable::Local(output.0),
							}),
						},
					},
				);
			}

			let add = self.symbol_generator.fresh();

			let left = self.symbol_generator.fresh();
			let add_inner_closure = self.symbol_generator.fresh();
			self.procedures.insert(
				FireflyProcedureLabel(add),
				FireflyProcedure {
					fixpoint_variable: None,
					environment_parameters: HashSet::new(),
					parameter: FireflyBindingLabel(left),
					body: FireflyTerm::AssignClosure {
						binding: FireflyBindingLabel(add_inner_closure),
						procedure: add_inner,
						environment_parameters_to_arguments: HashMap::from([(left_inner, FireflyBindingLabel(left))]),
						rest: Box::new(FireflyTerm::Jump {
							continuation_label: None,
							argument: FireflyVariable::Local(add_inner_closure),
						}),
					},
				},
			);

			intrinsics.insert(
				"add".to_owned(),
				FireflyValue::Closure(FireflyProcedureLabel(add), HashMap::new()),
			);
		}

		{
			let add2 = self.symbol_generator.fresh();
			let input = self.symbol_generator.fresh();
			let left = self.symbol_generator.fresh();
			let right = self.symbol_generator.fresh();
			let output = self.symbol_generator.fresh();
			self.procedures.insert(
				FireflyProcedureLabel(add2),
				FireflyProcedure {
					fixpoint_variable: None,
					environment_parameters: HashSet::new(),
					parameter: FireflyBindingLabel(input),
					body: FireflyTerm::AssignOperation {
						binding: FireflyBindingLabel(left),
						operation: FireflyOperation::Projection(FireflyVariable::Local(input), 0),
						rest: Box::new(FireflyTerm::AssignOperation {
							binding: FireflyBindingLabel(right),
							operation: FireflyOperation::Projection(FireflyVariable::Local(input), 1),
							rest: Box::new(FireflyTerm::AssignOperation {
								binding: FireflyBindingLabel(output),
								operation: FireflyOperation::Add([FireflyVariable::Local(left), FireflyVariable::Local(right)]),
								rest: Box::new(FireflyTerm::Jump {
									continuation_label: None,
									argument: FireflyVariable::Local(output),
								}),
							}),
						}),
					},
				},
			);
			intrinsics.insert(
				"add2".to_owned(),
				FireflyValue::Closure(FireflyProcedureLabel(add2), HashMap::new()),
			);
		}

		intrinsics
	}
}

fn lookup(
	intrinsics: &HashMap<String, FireflyValue>,
	environment: &HashMap<FireflyBindingLabel, FireflyValue>,
	variable: &FireflyVariable,
) -> Option<FireflyValue> {
	match variable {
		FireflyVariable::Local(local) => environment.get(&FireflyBindingLabel(*local)).cloned(),
		FireflyVariable::Global(global) => intrinsics.get(global).cloned(),
	}
}

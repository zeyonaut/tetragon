use std::{collections::HashMap, env::var, hash::Hash, ops::Index, sync::Arc};

use crate::utility::slice::Slice;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum CypressVariable {
	Auto(u64),
	Name(String),
}

#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct CypressLabel(pub u64);

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CypressType {
	Unity,
	Polarity,
	Integer,
	Power { domain: Box<Self>, codomain: Box<Self> },
	Product(Vec<Self>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CypressValue {
	Unity,
	Polarity(bool),
	Integer(i64),
	Tuple(Vec<Self>),
	Function(Arc<CypressFunction>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CypressOperation {
	EqualsQuery([CypressVariable; 2]),
	Projection(CypressVariable, usize),
	Add([CypressVariable; 2]),
	Pair(Slice<CypressVariable>),
}

impl CypressOperation {
	fn evaluate(self, variables: &HashMap<CypressVariable, CypressValue>) -> Option<CypressValue> {
		use CypressValue::*;
		match self {
			CypressOperation::EqualsQuery([x, y]) => Some(Polarity(variables.get(&x)? == variables.get(&y)?)),
			CypressOperation::Projection(tuple, index) => {
				if let Tuple(parts) = variables.get(&tuple)? {
					parts.get(index).cloned()
				} else {
					None
				}
			},
			CypressOperation::Add([x, y]) => {
				if let (Some(Integer(x)), Some(Integer(y))) = (variables.get(&x), variables.get(&y)) {
					Some(Integer(x + y))
				} else {
					None
				}
			},
			CypressOperation::Pair(parts) => {
				let parts = parts
					.as_ref()
					.into_iter()
					.map(|variable| variables.get(&variable))
					.collect::<Option<Vec<_>>>()?
					.into_iter()
					.cloned()
					.collect();
				Some(Tuple(parts))
			},
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CypressTerm {
	AssignValue {
		binding: CypressVariable,
		ty: CypressType,
		value: CypressValue,
		rest: Box<Self>,
	},
	AssignOperation {
		binding: CypressVariable,
		// FIXME: Commented out because it's annoying to get the type of a tuple.
		//ty: CypressType,
		operation: CypressOperation,
		rest: Box<Self>,
	},
	DeclareFunction {
		binding: CypressVariable,
		fixpoint_name: Option<CypressVariable>,
		domain: CypressType,
		codomain: CypressType,
		continuation: CypressLabel,
		parameter: CypressVariable,
		body: Box<Self>,
		rest: Box<Self>,
	},
	DeclareContinuation {
		label: CypressLabel,
		domain: CypressType,
		parameter: CypressVariable,
		body: Box<Self>,
		rest: Box<Self>,
	},
	CaseSplit {
		scrutinee: CypressVariable,
		yes_continuation: CypressLabel,
		no_continuation: CypressLabel,
	}, // Continuations should have unit domain. (For now.) Scrutinee should be a polarity.
	Apply {
		function: CypressVariable,
		continuation: CypressLabel,
		argument: CypressVariable,
	},
	Continue {
		label: CypressLabel,
		argument: CypressVariable,
	},
	Halt {
		argument: CypressVariable,
	},
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CypressFunction {
	fixpoint_variable: Option<CypressVariable>,
	returner: CypressLabel,
	parameter: CypressVariable,
	body: CypressTerm,
	variables: HashMap<CypressVariable, CypressValue>,
}

#[derive(Clone, Debug)]
struct CypressContinuation {
	parameter: CypressVariable,
	body: CypressTerm,
	variables: HashMap<CypressVariable, CypressValue>,
	continuations: HashMap<CypressLabel, Arc<CypressContinuation>>,
}

impl CypressTerm {
	pub fn evaluate(self) -> Option<CypressValue> {
		let mut term = self;
		let mut variables: HashMap<CypressVariable, CypressValue> = HashMap::new();
		let mut continuations: HashMap<CypressLabel, Arc<CypressContinuation>> = HashMap::new();

		insert_intrinsics(&mut variables);

		loop {
			match term.clone() {
				CypressTerm::AssignValue {
					binding,
					ty: _,
					value,
					rest,
				} => {
					variables.insert(binding, value);

					term = *rest;
					continue;
				},
				CypressTerm::AssignOperation {
					binding,
					//ty: _,
					operation,
					rest,
				} => {
					let value = operation.evaluate(&variables)?;
					variables.insert(binding, value);

					term = *rest;
					continue;
				},
				CypressTerm::DeclareFunction {
					binding,
					fixpoint_name,
					domain: _,
					codomain: _,
					continuation,
					parameter,
					body,
					rest,
				} => {
					variables.insert(
						binding,
						CypressValue::Function(Arc::new(CypressFunction {
							fixpoint_variable: fixpoint_name,
							returner: continuation,
							parameter,
							body: *body,
							variables: variables.clone(),
						})),
					);

					term = *rest;
					continue;
				},
				CypressTerm::DeclareContinuation {
					label,
					domain: _,
					parameter,
					body,
					rest,
				} => {
					continuations.insert(
						label,
						Arc::new(CypressContinuation {
							parameter,
							body: *body,
							variables: variables.clone(),
							continuations: continuations.clone(),
						}),
					);

					term = *rest;
					continue;
				},
				CypressTerm::CaseSplit {
					scrutinee,
					yes_continuation,
					no_continuation,
				} => {
					if let CypressValue::Polarity(scrutinee) = variables.get(&scrutinee)? {
						let continuation_label = if *scrutinee { yes_continuation } else { no_continuation };

						let continuation = continuations.get(&continuation_label)?;
						// FIXME: It's dirty, but we'll just forget about the argument for now. It's trivial and would have to be fresh, anyway.
						// NOTE: We presume that branch continuations are never recursive, too.

						term = continuation.body.clone();
						(variables, continuations) = (continuation.variables.clone(), continuation.continuations.clone());
						continue;
					} else {
						break None;
					}
				},
				CypressTerm::Apply {
					function: function_variable,
					continuation: returner_label,
					argument,
				} => {
					let function = variables.get(&function_variable)?;
					if let CypressValue::Function(function) = function {
						let mut next_variables = function.variables.clone();
						let mut next_continuations = HashMap::new();
						next_variables.insert(function.parameter.clone(), variables.get(&argument)?.clone());
						if let Some(fixpoint_variable) = &function.fixpoint_variable {
							next_variables.insert(fixpoint_variable.clone(), CypressValue::Function(function.clone()));
						}
						next_continuations.insert(function.returner.clone(), continuations.get(&returner_label)?.clone());

						term = function.body.clone();

						// NOTE: The following two loops are used to support tuples. I'm not entirely sure that these scoping rules are technically correct...
						for (variable, value) in variables {
							next_variables.entry(variable).or_insert(value);
						}

						(variables, continuations) = (next_variables, next_continuations);
						continue;
					} else {
						break None;
					}
				},
				CypressTerm::Continue { label, argument } => {
					let continuation = continuations.get(&label)?;
					let mut next_variables = continuation.variables.clone();
					let mut next_continuations = continuation.continuations.clone();
					next_variables.insert(continuation.parameter.clone(), variables.get(&argument)?.clone());
					next_continuations.insert(label, continuation.clone());

					// NOTE: The following two loops are used to support tuples. I'm not entirely sure that these scoping rules are technically correct...
					for (variable, value) in variables {
						next_variables.entry(variable).or_insert(value);
					}

					term = continuation.body.clone();
					(variables, continuations) = (next_variables, next_continuations);
					continue;
				},
				CypressTerm::Halt { argument } => break variables.get(&argument).cloned(),
			}
		}
	}
}

// FIXME: Figure out something saner for the returner labels (they need to be globally unique, or at least... (wait, why do they have to be unique again? Experimentally, it doesn't work if they aren't, but why doesn't it work?))
// Can we use `None` for returners?
fn insert_intrinsics(functions: &mut HashMap<CypressVariable, CypressValue>) {
	functions.insert(
		CypressVariable::Name("add".to_owned()),
		CypressValue::Function(Arc::new(CypressFunction {
			fixpoint_variable: None,
			returner: CypressLabel(10000),
			parameter: CypressVariable::Name("left".to_owned()),
			body: CypressTerm::DeclareFunction {
				binding: CypressVariable::Name("add_inner".to_owned()),
				fixpoint_name: None,
				domain: CypressType::Integer,
				codomain: CypressType::Integer,
				continuation: CypressLabel(10001),
				parameter: CypressVariable::Name("right".to_owned()),
				body: Box::new(CypressTerm::AssignOperation {
					binding: CypressVariable::Name("output".to_owned()),
					//ty: CypressType::Integer,
					operation: CypressOperation::Add([
						CypressVariable::Name("left".to_owned()),
						CypressVariable::Name("right".to_owned()),
					]),
					rest: Box::new(CypressTerm::Continue {
						label: CypressLabel(10001),
						argument: CypressVariable::Name("output".to_owned()),
					}),
				}),
				rest: Box::new(CypressTerm::Continue {
					label: CypressLabel(10000),
					argument: CypressVariable::Name("add_inner".to_owned()),
				}),
			},
			variables: HashMap::new(),
		})),
	);
}

use std::{collections::HashMap, hash::Hash, sync::Arc};

use crate::{translator::symbol::SymbolGenerator, utility::slice::Slice};

pub type CypressBindingLabel = u64;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum CypressVariable {
	Local(CypressBindingLabel),
	Name(String),
}

pub type CypressContinuationLabel = u64;

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

// Primitives are essentially nullary operations that can't fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CypressPrimitive {
	Unity,
	Polarity(bool),
	Integer(i64),
}

impl CypressPrimitive {
	fn evaluate(self) -> CypressValue {
		match self {
			Self::Unity => CypressValue::Unity,
			Self::Polarity(x) => CypressValue::Polarity(x),
			Self::Integer(x) => CypressValue::Integer(x),
		}
	}
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
			CypressOperation::Pair(parts) => Some(Tuple(
				parts
					.as_ref()
					.into_iter()
					.map(|variable| variables.get(&variable).cloned())
					.collect::<Option<Vec<_>>>()?,
			)),
		}
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CypressTerm {
	AssignValue {
		binding: CypressBindingLabel,
		ty: CypressType,
		value: CypressPrimitive,
		rest: Box<Self>,
	},
	AssignOperation {
		binding: CypressBindingLabel,
		operation: CypressOperation,
		rest: Box<Self>,
	},
	DeclareFunction {
		binding: CypressBindingLabel,
		fixpoint_name: Option<CypressBindingLabel>,
		domain: CypressType,
		codomain: CypressType,
		parameter: CypressBindingLabel,
		body: Box<Self>,
		rest: Box<Self>,
	},
	DeclareContinuation {
		label: CypressContinuationLabel,
		domain: CypressType,
		parameter: CypressBindingLabel,
		body: Box<Self>,
		rest: Box<Self>,
	},
	CaseSplit {
		scrutinee: CypressVariable,
		yes_continuation: CypressContinuationLabel,
		no_continuation: CypressContinuationLabel,
	}, // Continuations should have unit domain. (For now.) Scrutinee should be a polarity.
	Apply {
		function: CypressVariable,
		continuation: Option<CypressContinuationLabel>,
		argument: CypressVariable,
	},
	Continue {
		continuation_label: Option<CypressContinuationLabel>,
		argument: CypressVariable,
	},
	Halt {
		argument: CypressVariable,
	},
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CypressFunction {
	pub identifier: CypressVariable,
	pub fixpoint_variable: Option<CypressBindingLabel>,
	pub parameter: CypressBindingLabel,
	pub body: CypressTerm,
	pub variables: HashMap<CypressVariable, CypressValue>,
}

#[derive(Clone, Debug)]
struct CypressContinuation {
	parameter: CypressBindingLabel,
	body: CypressTerm,
	variables: HashMap<CypressVariable, CypressValue>,
	continuations: HashMap<CypressContinuationLabel, Arc<CypressContinuation>>,
}

impl CypressTerm {
	pub fn evaluate(self, mut symbol_generator: SymbolGenerator) -> Option<CypressValue> {
		let mut term = self;
		let mut variables: HashMap<CypressVariable, CypressValue> = HashMap::new();
		let mut continuations: HashMap<CypressContinuationLabel, Arc<CypressContinuation>> = HashMap::new();
		let mut returners: Vec<Arc<CypressContinuation>> = Vec::new();

		insert_intrinsics(&mut variables, &mut symbol_generator);

		loop {
			match term.clone() {
				CypressTerm::AssignValue {
					binding,
					ty: _,
					value,
					rest,
				} => {
					variables.insert(CypressVariable::Local(binding), value.evaluate());

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
					variables.insert(CypressVariable::Local(binding), value);

					term = *rest;
					continue;
				},
				CypressTerm::DeclareFunction {
					binding,
					fixpoint_name,
					domain: _,
					codomain: _,
					parameter,
					body,
					rest,
				} => {
					variables.insert(
						CypressVariable::Local(binding),
						CypressValue::Function(Arc::new(CypressFunction {
							identifier: CypressVariable::Local(binding),
							fixpoint_variable: fixpoint_name,
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
						let next_continuations = HashMap::new();
						next_variables.insert(
							CypressVariable::Local(function.parameter.clone()),
							variables.get(&argument)?.clone(),
						);
						if let Some(fixpoint_variable) = &function.fixpoint_variable {
							next_variables.insert(
								CypressVariable::Local(fixpoint_variable.clone()),
								CypressValue::Function(function.clone()),
							);
						}
						if let Some(returner_label) = returner_label {
							returners.push(continuations.get(&returner_label)?.clone());
						}

						term = function.body.clone();

						(variables, continuations) = (next_variables, next_continuations);
						continue;
					} else {
						break None;
					}
				},
				CypressTerm::Continue {
					continuation_label: label,
					argument,
				} => {
					let continuation = if let Some(label) = label {
						continuations.get(&label).cloned()?
					} else if let Some(returner) = returners.pop() {
						returner
					} else {
						break variables.get(&argument).cloned();
					};

					let mut next_variables = continuation.variables.clone();
					let mut next_continuations = continuation.continuations.clone();
					next_variables.insert(
						CypressVariable::Local(continuation.parameter.clone()),
						variables.get(&argument)?.clone(),
					);
					if let Some(label) = label {
						next_continuations.insert(label, continuation.clone());
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

fn insert_intrinsics(variables: &mut HashMap<CypressVariable, CypressValue>, symbol_generator: &mut SymbolGenerator) {
	{
		let left = symbol_generator.fresh();
		let right = symbol_generator.fresh();
		let add_inner = symbol_generator.fresh();
		let output = symbol_generator.fresh();
		variables.insert(
			CypressVariable::Name("add".to_owned()),
			CypressValue::Function(Arc::new(CypressFunction {
				identifier: CypressVariable::Name("add".to_owned()),
				fixpoint_variable: None,
				parameter: left,
				body: CypressTerm::DeclareFunction {
					binding: add_inner,
					fixpoint_name: None,
					domain: CypressType::Integer,
					codomain: CypressType::Integer,
					parameter: right,
					body: Box::new(CypressTerm::AssignOperation {
						binding: output,
						operation: CypressOperation::Add([CypressVariable::Local(left), CypressVariable::Local(right)]),
						rest: Box::new(CypressTerm::Continue {
							continuation_label: None,
							argument: CypressVariable::Local(output),
						}),
					}),
					rest: Box::new(CypressTerm::Continue {
						continuation_label: None,
						argument: CypressVariable::Local(add_inner),
					}),
				},
				variables: HashMap::new(),
			})),
		);
	}
	{
		let tup = symbol_generator.fresh();
		let left = symbol_generator.fresh();
		let right = symbol_generator.fresh();
		let output = symbol_generator.fresh();
		variables.insert(
			CypressVariable::Name("add2".to_owned()),
			CypressValue::Function(Arc::new(CypressFunction {
				identifier: CypressVariable::Name("add2".to_owned()),
				fixpoint_variable: None,
				parameter: tup,
				body: CypressTerm::AssignOperation {
					binding: left,
					operation: CypressOperation::Projection(CypressVariable::Local(tup), 0),
					rest: Box::new(CypressTerm::AssignOperation {
						binding: right,
						operation: CypressOperation::Projection(CypressVariable::Local(tup), 1),
						rest: Box::new(CypressTerm::AssignOperation {
							binding: output,
							operation: CypressOperation::Add([CypressVariable::Local(left), CypressVariable::Local(right)]),
							rest: Box::new(CypressTerm::Continue {
								continuation_label: None,
								argument: CypressVariable::Local(output),
							}),
						}),
					}),
				},
				variables: HashMap::new(),
			})),
		);
	}
}

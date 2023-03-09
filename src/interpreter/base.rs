use std::sync::Arc;

use crate::translator::elaborator::{BaseExpression, BaseTerm};

#[derive(Clone)]
pub struct RecursiveFunction {
	fixpoint_name: String,
	function: Arc<dyn (Fn(Self, BaseValue) -> Option<BaseValue>)>,
}

#[derive(Clone)]
pub enum BaseValue {
	Polarity(bool),
	Integer(i64),
	Function(Arc<dyn (Fn(Self) -> Option<Self>)>),
	RecursiveFunction(RecursiveFunction),
}

impl core::fmt::Debug for BaseValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Polarity(x) => f.write_str(&x.to_string()),
			Self::Integer(x) => f.write_str(&x.to_string()),
			Self::Function(_) => f.write_str("<function>"),
			Self::RecursiveFunction(_) => f.write_str("<recursive function>"),
		}
	}
}

#[derive(Clone)]
pub struct BaseEnvironment {
	pub values: Vec<(String, BaseValue)>,
}

impl BaseEnvironment {
	pub fn new(values: Vec<(String, BaseValue)>) -> Self {
		Self { values }
	}

	pub fn lookup(&self, index_name: &str) -> Option<BaseValue> {
		for (name, value) in &self.values {
			if name == index_name {
				return Some(value.clone());
			}
		}
		None
	}

	pub fn extend(&self, name: &str, value: BaseValue) -> Self {
		Self {
			values: {
				let mut values = self.values.clone();
				values.push((name.to_owned(), value.into()));
				values
			},
		}
	}
}

pub fn interpret_base(base_term: BaseExpression, environment: BaseEnvironment) -> Option<BaseValue> {
	use BaseTerm::*;
	match base_term.term {
		Polarity(x) => Some(BaseValue::Polarity(x)),
		Integer(x) => Some(BaseValue::Integer(x)),
		Name(name) => environment.lookup(&name),
		Function {
			fixpoint_name,
			parameter,
			domain: _,
			codomain: _,
			body,
		} => {
			if let Some(fixpoint_name) = fixpoint_name {
				Some(BaseValue::RecursiveFunction(RecursiveFunction {
					fixpoint_name: fixpoint_name.clone(),
					function: Arc::new(move |fixpoint, value| {
						interpret_base(
							(*body).clone(),
							environment
								.extend(&fixpoint.fixpoint_name.clone(), BaseValue::RecursiveFunction(fixpoint))
								.extend(&parameter, value),
						)
					}),
				}))
			} else {
				Some(BaseValue::Function(Arc::new(move |value| {
					interpret_base((*body).clone(), environment.extend(&parameter, value))
				})))
			}
		},
		Application { function, argument } => {
			let function = interpret_base(*function, environment.clone())?;
			let argument = interpret_base(*argument, environment)?;
			match function {
				BaseValue::Function(function) => function(argument),
				BaseValue::RecursiveFunction(function) => (function.function.clone())(function, argument),
				_ => None,
			}
		},
		Assignment {
			assignee: binding,
			definition,
			rest,
		} => {
			let definition = interpret_base(*definition, environment.clone())?;
			interpret_base(*rest, environment.extend(&binding, definition))
		},
		EqualityQuery { left, right } => {
			let left = interpret_base(*left, environment.clone())?;
			let right = interpret_base(*right, environment)?;
			match (left, right) {
				(BaseValue::Polarity(x), BaseValue::Polarity(y)) => Some(BaseValue::Polarity(x == y)),
				(BaseValue::Integer(x), BaseValue::Integer(y)) => Some(BaseValue::Polarity(x == y)),
				_ => None,
			}
		},
		CaseSplit { scrutinee, cases } => {
			let scrutinee = interpret_base(*scrutinee, environment.clone())?;
			let scrutinee = match scrutinee {
				BaseValue::Polarity(x) => Some(x),
				_ => None,
			}?;
			let mut expression = None;
			for (pattern, body) in cases {
				if scrutinee == pattern {
					expression = Some(interpret_base(*body, environment)?);
					break;
				}
			}
			expression
		},
	}
}

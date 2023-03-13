use std::sync::Arc;

use crate::translator::label::Label;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaseVariable {
	Auto(Label),
	Name(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaseTerm {
	Polarity(bool),
	Integer(i64),
	Name(BaseType, BaseVariable),
	Tuple(Vec<(BaseType, Self)>),
	Projection {
		ty: BaseType,
		tuple: Box<Self>,
		index: usize,
	},
	Function {
		domain: BaseType,
		codomain: BaseType,
		fixpoint_name: Option<Label>,
		parameter: Label,
		body: Box<Self>,
	},
	Application {
		ty: BaseType,
		function: Box<Self>,
		argument: Box<Self>,
	},
	Assignment {
		ty: BaseType,
		assignee: Label,
		definition: Box<Self>,
		rest: Box<Self>,
	},
	EqualityQuery {
		left: Box<Self>,
		right: Box<Self>,
	},
	CaseSplit {
		ty: BaseType,
		scrutinee: Box<Self>,
		cases: Vec<(bool, Box<Self>)>,
	},
}

impl BaseTerm {
	pub fn ty(&self) -> BaseType {
		match self {
			Self::Polarity(_) => BaseType::Polarity,
			Self::Integer(_) => BaseType::Integer,
			Self::Name(ty, _) => ty.clone(),
			Self::Tuple(typed_terms) => BaseType::Product(typed_terms.iter().map(|(ty, _)| ty).cloned().collect()),
			Self::Projection { ty, tuple: _, index: _ } => ty.clone(),
			Self::Function {
				domain,
				codomain,
				fixpoint_name: _,
				parameter: _,
				body: _,
			} => BaseType::Power {
				domain: Box::new(domain.clone()),
				codomain: Box::new(codomain.clone()),
			},
			Self::Application {
				ty,
				function: _,
				argument: _,
			} => ty.clone(),
			Self::Assignment {
				ty,
				assignee: _,
				definition: _,
				rest: _,
			} => ty.clone(),
			Self::EqualityQuery { left: _, right: _ } => BaseType::Polarity,
			Self::CaseSplit {
				ty,
				scrutinee: _,
				cases: _,
			} => ty.clone(),
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaseType {
	//	Zero,
	//	One,
	Polarity,
	Integer,
	Product(Vec<Self>),
	Power { domain: Box<Self>, codomain: Box<Self> },
}

#[derive(Clone)]
pub struct RecursiveFunction {
	fixpoint_name: Label,
	function: Arc<dyn (Fn(Self, BaseValue) -> Option<BaseValue>)>,
}

#[derive(Clone)]
pub enum BaseValue {
	Polarity(bool),
	Integer(i64),
	Tuple(Vec<Self>),
	Function(Arc<dyn (Fn(Self) -> Option<Self>)>),
	RecursiveFunction(RecursiveFunction),
}

impl core::fmt::Debug for BaseValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Polarity(x) => f.write_str(&x.to_string()),
			Self::Integer(x) => f.write_str(&x.to_string()),
			Self::Tuple(x) => x.as_slice().fmt(f),
			Self::Function(_) => f.write_str("<function>"),
			Self::RecursiveFunction(_) => f.write_str("<recursive function>"),
		}
	}
}

#[derive(Clone)]
pub struct BaseEnvironment {
	pub values: Vec<(BaseVariable, BaseValue)>,
}

impl BaseEnvironment {
	pub fn new(values: Vec<(BaseVariable, BaseValue)>) -> Self {
		Self { values }
	}

	pub fn lookup(&self, index_name: &BaseVariable) -> Option<BaseValue> {
		for (name, value) in &self.values {
			if name == index_name {
				return Some(value.clone());
			}
		}
		None
	}

	pub fn extend(&self, name: BaseVariable, value: BaseValue) -> Self {
		Self {
			values: {
				let mut values = self.values.clone();
				values.push((name, value.into()));
				values
			},
		}
	}
}

pub fn interpret_base(base_term: BaseTerm, environment: BaseEnvironment) -> Option<BaseValue> {
	use BaseTerm::*;
	match base_term {
		Polarity(x) => Some(BaseValue::Polarity(x)),
		Integer(x) => Some(BaseValue::Integer(x)),
		Name(_, name) => environment.lookup(&name),
		Tuple(tuple) => Some(BaseValue::Tuple(
			tuple
				.into_iter()
				.map(|(_, term)| interpret_base(term, environment.clone()))
				.collect::<Option<_>>()?,
		)),
		Projection { ty: _, tuple, index } => {
			let tuple = interpret_base(*tuple, environment)?;
			if let BaseValue::Tuple(tuple) = tuple {
				tuple.get(index).cloned()
			} else {
				None
			}
		},
		Function {
			fixpoint_name,
			parameter,
			domain: _,
			codomain: _,
			body,
		} => {
			if let Some(fixpoint_name) = fixpoint_name {
				Some(BaseValue::RecursiveFunction(RecursiveFunction {
					fixpoint_name,
					function: Arc::new(move |fixpoint, value| {
						interpret_base(
							(*body).clone(),
							environment
								.extend(
									BaseVariable::Auto(fixpoint.fixpoint_name),
									BaseValue::RecursiveFunction(fixpoint),
								)
								.extend(BaseVariable::Auto(parameter), value),
						)
					}),
				}))
			} else {
				Some(BaseValue::Function(Arc::new(move |value| {
					interpret_base((*body).clone(), environment.extend(BaseVariable::Auto(parameter), value))
				})))
			}
		},
		Application {
			ty: _,
			function,
			argument,
		} => {
			let function = interpret_base(*function, environment.clone())?;
			let argument = interpret_base(*argument, environment)?;
			match function {
				BaseValue::Function(function) => function(argument),
				BaseValue::RecursiveFunction(function) => (function.function.clone())(function, argument),
				_ => None,
			}
		},
		Assignment {
			ty: _,
			assignee: binding,
			definition,
			rest,
		} => {
			let definition = interpret_base(*definition, environment.clone())?;
			interpret_base(*rest, environment.extend(BaseVariable::Auto(binding), definition))
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
		CaseSplit { ty: _, scrutinee, cases } => {
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

pub fn evaluate_base(base_term: BaseTerm) -> Option<BaseValue> {
	interpret_base(
		base_term,
		BaseEnvironment::new(vec![(
			BaseVariable::Name("add".to_owned()),
			BaseValue::Function(Arc::new(|value_0| match value_0 {
				BaseValue::Integer(x) => Some(BaseValue::Function(Arc::new(move |value_1| match value_1 {
					BaseValue::Integer(y) => Some(BaseValue::Integer(x + y)),
					_ => None,
				}))),
				_ => None,
			})),
		)]),
	)
}

use std::sync::Arc;

// TODO: Does this need to be generic? Well, I guess we'll see.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaseTerm<V> {
	Polarity(bool),
	Integer(i64),
	Name(BaseType, V),
	Tuple(Vec<(BaseType, Self)>),
	Projection {
		ty: BaseType,
		tuple: Box<Self>,
		index: usize,
	},
	Function {
		domain: BaseType,
		codomain: BaseType,
		fixpoint_name: Option<String>,
		parameter: String,
		body: Box<Self>,
	},
	Application {
		ty: BaseType,
		function: Box<Self>,
		argument: Box<Self>,
	},
	Assignment {
		ty: BaseType,
		assignee: String,
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

impl<V> BaseTerm<V> {
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
	fixpoint_name: String,
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

pub fn interpret_base(base_term: BaseTerm<String>, environment: BaseEnvironment) -> Option<BaseValue> {
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

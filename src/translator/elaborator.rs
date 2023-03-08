use crate::{parser::parser::*, util::slice::match_slice};

// TODO: Does this need to be generic? Well, I guess we'll see.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaseTerm<T> {
	Polarity(bool),
	Integer(i64),
	Name(String),
	Function {
		recursive: Option<String>,
		binding: String,
		ty: BaseType,
		body: Box<T>,
	},
	Application {
		function: Box<T>,
		argument: Box<T>,
	},
	Assignment {
		binding: String,
		definition: Box<T>,
		rest: Box<T>,
	},
	EqualityQuery {
		left: Box<T>,
		right: Box<T>,
	},
	CaseSplit {
		scrutinee: Box<T>,
		cases: Vec<(bool, Box<T>)>,
	},
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BaseType {
	//	Zero,
	//	One,
	Polarity,
	Integer,
	Power { domain: Box<Self>, codomain: Box<Self> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BaseExpression {
	pub term: BaseTerm<Self>,
	pub ty: BaseType,
}

#[derive(Clone)]
pub struct Context {
	tys: Vec<(String, BaseType)>,
}

impl Context {
	pub fn new(tys: Vec<(String, BaseType)>) -> Self {
		Self { tys }
	}

	pub fn find(&self, name: &str) -> Option<BaseType> {
		for (test, ty) in self.tys.iter().rev() {
			if test == name {
				return Some(ty.clone());
			}
		}
		None
	}

	pub fn extend(&self, name: String, ty: BaseType) -> Self {
		Self {
			tys: {
				let mut tys = self.tys.clone();
				tys.push((name.to_owned(), ty.into()));
				tys
			},
		}
	}
}

// TODO: Should this be a part of elaboration? That would required types in the context. I think something like that is necessary for user-defined types.
pub fn elaborate_ty(parsed_ty: ParsedType) -> Option<BaseType> {
	match parsed_ty {
		ParsedType::Name(_) => todo!(),
		ParsedType::Power { domain, codomain } => {
			elaborate_ty(*domain)
				.zip(elaborate_ty(*codomain))
				.map(|(domain, codomain)| BaseType::Power {
					domain: Box::new(domain),
					codomain: Box::new(codomain),
				})
		},
		ParsedType::Polarity => Some(BaseType::Polarity),
		ParsedType::Integer => Some(BaseType::Integer),
	}
}

// TODO: This needs to get cleaned up as it's really messy (in particular: completely different styles in each branch, no error handling with Result).
// TODO: Do we need or want to un-elaborate by removing types? Do we need to convert let bindings to function applications here too? For the latter, we should be careful of execution order.
pub fn elaborate(context: Context, parsed_term: ParsedTerm, expected_ty: Option<BaseType>) -> Option<BaseExpression> {
	match (expected_ty, parsed_term) {
		(None, ParsedTerm::Polarity(pole)) => Some(BaseExpression {
			term: BaseTerm::Polarity(pole),
			ty: BaseType::Polarity,
		}),
		(None, ParsedTerm::Integer(x)) => Some(BaseExpression {
			term: BaseTerm::Integer(x),
			ty: BaseType::Integer,
		}),
		(None, ParsedTerm::Name(name)) => context.find(&name).and_then(|ty| {
			Some(BaseExpression {
				term: BaseTerm::Name(name),
				ty: ty,
			})
		}),
		(
			None,
			ParsedTerm::Function {
				binding,
				domain,
				codomain,
				body,
			},
		) => elaborate_ty(domain)
			.zip(elaborate_ty(codomain))
			.and_then(|(domain, codomain)| {
				elaborate(context.extend(binding.clone(), domain.clone()), *body, Some(codomain.clone())).map(|body| {
					BaseExpression {
						term: BaseTerm::Function {
							recursive: None,
							binding,
							ty: domain.clone(),
							body: Box::new(body),
						},
						ty: BaseType::Power {
							domain: Box::new(domain),
							codomain: Box::new(codomain),
						},
					}
				})
			}),
		(
			None,
			ParsedTerm::Fixpoint {
				binding: mu_binding,
				body: mu_body,
			},
		) => {
			if let ParsedTerm::Function {
				binding: lambda_binding,
				domain,
				codomain,
				body: lambda_body,
			} = *mu_body.clone()
			{
				elaborate_ty(domain)
					.zip(elaborate_ty(codomain))
					.and_then(|(domain, codomain)| {
						elaborate(context.extend(
							mu_binding.clone(),
							BaseType::Power {
								domain: Box::new(domain.clone()),
								codomain: Box::new(codomain.clone()),
							},
						).extend(lambda_binding.clone(), domain.clone()), (*lambda_body).clone(), Some(codomain.clone())).map(|body| {
							BaseExpression {
								term: BaseTerm::Function {
									recursive: Some(mu_binding),
									binding: lambda_binding,
									ty: domain.clone(),
									body: Box::new(body),
								},
								ty: BaseType::Power {
									domain: Box::new(domain),
									codomain: Box::new(codomain),
								},
							}
						})
					})
			} else {
				None
			}
		},
		(None, ParsedTerm::Application { function, argument }) => {
			let function = elaborate(context.clone(), *function, None)?;
			if let BaseType::Power { domain, codomain } = function.ty.clone() {
				let argument = elaborate(context, *argument, Some(*domain))?;
				Some(BaseExpression {
					term: BaseTerm::Application {
						function: Box::new(function),
						argument: Box::new(argument),
					},
					ty: *codomain,
				})
			} else {
				None
			}
		},
		(
			None,
			ParsedTerm::Assignment {
				binding,
				definition,
				rest,
			},
		) => {
			let definition = elaborate(context.clone(), *definition, None)?;
			let rest = elaborate(context.extend(binding.clone(), definition.ty.clone()), *rest, None)?;
			Some(BaseExpression {
				ty: rest.ty.clone(),
				term: BaseTerm::Assignment {
					binding,
					definition: Box::new(definition),
					rest: Box::new(rest),
				},
			})
		},
		(None, ParsedTerm::EqualityQuery { left, right }) => {
			let left = elaborate(context.clone(), *left, None)?;
			let right = elaborate(context, *right, Some(left.ty.clone()))?;
			Some(BaseExpression {
				term: BaseTerm::EqualityQuery {
					left: Box::new(left),
					right: Box::new(right),
				},
				ty: BaseType::Polarity,
			})
		},
		(None, ParsedTerm::CaseSplit { scrutinee, cases }) => {
			let scrutinee = elaborate(context.clone(), *scrutinee, None)?;
			match_slice! {cases.cases.into_boxed_slice();
				[(case_0, body_0), (case_1, body_1)] => {
					// Ensure that the case split is exhaustive.
					if case_0 ^ case_1 {
						let body_0 = elaborate(context.clone(), *body_0, None)?;
						let body_1 = elaborate(context, *body_1, Some(body_0.ty.clone()))?;
						Some(BaseExpression {
							ty: body_0.ty.clone(),
							term: BaseTerm::CaseSplit {
								scrutinee: Box::new(scrutinee),
								cases: vec![(case_0, Box::new(body_0)), (case_1, Box::new(body_1))],
							},
						})
					} else {
						None
					}
				},
				_ => None,
			}
		},
		(Some(expected_ty), parsed_term) => {
			elaborate(context, parsed_term, None).filter(|typed_term| typed_term.ty == expected_ty)
		},
	}
}

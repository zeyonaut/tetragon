use crate::{parser::parser::*, util::slice::match_slice};

// TODO: Does this need to be generic? Well, I guess we'll see.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term<T> {
	Polarity(bool),
	Integer(i64),
	Name(String),
	Function {
		binding: String,
		ty: Type,
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
pub enum Type {
	//	Zero,
	//	One,
	Polarity,
	Integer,
	Power { domain: Box<Self>, codomain: Box<Self> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedTerm {
	term: Term<Self>,
	ty: Type,
}

#[derive(Clone)]
pub struct Context {
	tys: Vec<(String, Type)>,
}

impl Context {
	pub fn new(tys: Vec<(String, Type)>) -> Self {
		Self { tys }
	}

	pub fn find(&self, name: &str) -> Option<Type> {
		for (test, ty) in self.tys.iter().rev() {
			if test == name {
				return Some(ty.clone());
			}
		}
		None
	}

	pub fn extend(&self, name: String, ty: Type) -> Self {
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
pub fn elaborate_ty(parsed_ty: ParsedType) -> Option<Type> {
	match parsed_ty {
		ParsedType::Name(_) => todo!(),
		ParsedType::Power { domain, codomain } => {
			elaborate_ty(*domain)
				.zip(elaborate_ty(*codomain))
				.map(|(domain, codomain)| Type::Power {
					domain: Box::new(domain),
					codomain: Box::new(codomain),
				})
		},
		ParsedType::Polarity => Some(Type::Polarity),
		ParsedType::Integer => Some(Type::Integer),
	}
}

// TODO: This needs to get cleaned up as it's really messy (in particular: completely different styles in each branch, no error handling with Result).
// TODO: Do we need or want to un-elaborate by removing types? Do we need to convert let bindings to function applications here too? For the latter, we should be careful of execution order.
pub fn elaborate(context: Context, parsed_term: ParsedTerm, expected_ty: Option<Type>) -> Option<TypedTerm> {
	match (expected_ty, parsed_term) {
		(None, ParsedTerm::Polarity(pole)) => Some(TypedTerm {
			term: Term::Polarity(pole),
			ty: Type::Polarity,
		}),
		(None, ParsedTerm::Integer(x)) => Some(TypedTerm {
			term: Term::Integer(x),
			ty: Type::Integer,
		}),
		(None, ParsedTerm::Name(name)) => context.find(&name).and_then(|ty| {
			Some(TypedTerm {
				term: Term::Name(name),
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
					TypedTerm {
						term: Term::Function {
							binding,
							ty: domain.clone(),
							body: Box::new(body),
						},
						ty: Type::Power {
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
				binding: _,
				domain,
				codomain,
				body: _,
			} = *mu_body.clone()
			{
				elaborate_ty(domain)
					.zip(elaborate_ty(codomain))
					.and_then(|(domain, codomain)| {
						elaborate(
							context.extend(
								mu_binding,
								Type::Power {
									domain: Box::new(domain.clone()),
									codomain: Box::new(codomain.clone()),
								},
							),
							*mu_body,
							Some(Type::Power {
								domain: Box::new(domain.clone()),
								codomain: Box::new(codomain.clone()),
							}),
						)
					})
			} else {
				None
			}
		},
		(None, ParsedTerm::Application { function, argument }) => {
			let function = elaborate(context.clone(), *function, None)?;
			if let Type::Power { domain, codomain } = function.ty.clone() {
				let argument = elaborate(context, *argument, Some(*domain))?;
				Some(TypedTerm {
					term: Term::Application {
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
			Some(TypedTerm {
				ty: rest.ty.clone(),
				term: Term::Assignment {
					binding,
					definition: Box::new(definition),
					rest: Box::new(rest),
				},
			})
		},
		(None, ParsedTerm::EqualityQuery { left, right }) => {
			let left = elaborate(context.clone(), *left, None)?;
			let right = elaborate(context, *right, Some(left.ty.clone()))?;
			Some(TypedTerm {
				term: Term::EqualityQuery {
					left: Box::new(left),
					right: Box::new(right),
				},
				ty: Type::Polarity,
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
						Some(TypedTerm {
							ty: body_0.ty.clone(),
							term: Term::CaseSplit {
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

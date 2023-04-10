use std::collections::HashMap;

use super::label::{Label, LabelGenerator};
use crate::{
	interpreter::base::{BaseTerm, BaseType, BaseVariable},
	parser::parser::*,
	utility::slice::match_slice,
};

#[derive(Clone)]
pub struct Context {
	tys: Vec<(BaseVariable, BaseType)>,
}

impl Context {
	pub fn new(tys: Vec<(BaseVariable, BaseType)>) -> Self {
		Self { tys }
	}

	pub fn find(&self, name: &BaseVariable) -> Option<BaseType> {
		for (test, ty) in self.tys.iter().rev() {
			if test == name {
				return Some(ty.clone());
			}
		}
		None
	}

	pub fn extend(&self, name: BaseVariable, ty: BaseType) -> Self {
		Self {
			tys: {
				let mut tys = self.tys.clone();
				tys.push((name.to_owned(), ty.into()));
				tys
			},
		}
	}
}

pub fn elaborate_ty(parsed_ty: ParsedType) -> Option<BaseType> {
	match parsed_ty {
		ParsedType::Name(_) => unimplemented!(),
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
		ParsedType::Product(factors) => Some(BaseType::Product(
			factors.into_iter().map(elaborate_ty).collect::<Option<_>>()?,
		)),
	}
}

pub fn elaborate_term(
	context: Context,
	parsed_term: ParsedTerm,
	expected_ty: Option<BaseType>,
	names: &mut HashMap<Label, String>,
	numbers: &mut HashMap<String, Label>,
	symbol_generator: &mut LabelGenerator,
) -> Option<BaseTerm> {
	match (expected_ty, parsed_term) {
		(None, ParsedTerm::Polarity(pole)) => Some(BaseTerm::Polarity(pole)),
		(None, ParsedTerm::Integer(x)) => Some(BaseTerm::Integer(x)),
		(None, ParsedTerm::Name(name)) => {
			let variable = numbers
				.get(&name)
				.copied()
				.map_or(BaseVariable::Name(name), |number| BaseVariable::Auto(number));

			let ty = context.find(&variable)?;

			Some(BaseTerm::Name(ty, variable))
		},
		(None, ParsedTerm::Tuple(tuple)) => {
			let typed_terms = tuple
				.into_iter()
				.map(move |parsed_term| elaborate_term(context.clone(), parsed_term, None, names, numbers, symbol_generator))
				.collect::<Option<Vec<_>>>()
				.map(|v| {
					v.into_iter()
						.map(|expression| (expression.ty(), expression.clone()))
						.collect()
				})?;

			Some(BaseTerm::Tuple(typed_terms))
		},
		(None, ParsedTerm::Projection { tuple, index }) => {
			let tuple = elaborate_term(context, *tuple, None, names, numbers, symbol_generator)?;
			match tuple.ty() {
				BaseType::Product(product) => Some(BaseTerm::Projection {
					ty: product.get(index).cloned()?,
					tuple: Box::new(tuple),
					index,
				}),
				_ => None,
			}
		},
		(
			None,
			ParsedTerm::Function {
				parameter,
				domain,
				codomain,
				body,
			},
		) => {
			let domain = elaborate_ty(domain)?;
			let codomain = elaborate_ty(codomain)?;

			let shadowed_parameter_number = numbers.get(&parameter).copied();
			let [bound_parameter_number] = symbol_generator.fresh();
			names.insert(bound_parameter_number, parameter.clone());
			numbers.insert(parameter.clone(), bound_parameter_number);

			let body = elaborate_term(
				context.extend(BaseVariable::Auto(bound_parameter_number), domain.clone()),
				*body,
				Some(codomain.clone()),
				names,
				numbers,
				symbol_generator,
			)?;

			if let Some(shadowed_parameter_number) = shadowed_parameter_number {
				numbers.insert(parameter, shadowed_parameter_number);
			}

			Some(BaseTerm::Function {
				fixpoint_name: None,
				parameter: bound_parameter_number,
				domain,
				codomain,
				body: Box::new(body),
			})
		},
		(
			None,
			ParsedTerm::Fixpoint {
				binding: mu_binding,
				body: mu_body,
			},
		) => {
			if let ParsedTerm::Function {
				parameter,
				domain,
				codomain,
				body: lambda_body,
			} = *mu_body.clone()
			{
				let domain = elaborate_ty(domain)?;
				let codomain = elaborate_ty(codomain)?;

				let shadowed_fixpoint_number = numbers.get(&parameter).copied();
				let [bound_fixpoint_number] = symbol_generator.fresh();
				names.insert(bound_fixpoint_number, mu_binding.clone());
				numbers.insert(mu_binding.clone(), bound_fixpoint_number);

				let shadowed_parameter_number = numbers.get(&parameter).copied();
				let [bound_parameter_number] = symbol_generator.fresh();
				names.insert(bound_parameter_number, parameter.clone());
				numbers.insert(parameter.clone(), bound_parameter_number);

				let body = elaborate_term(
					context
						.extend(
							BaseVariable::Auto(bound_fixpoint_number),
							BaseType::Power {
								domain: Box::new(domain.clone()),
								codomain: Box::new(codomain.clone()),
							},
						)
						.extend(BaseVariable::Auto(bound_parameter_number), domain.clone()),
					(*lambda_body).clone(),
					Some(codomain.clone()),
					names,
					numbers,
					symbol_generator,
				)?;

				if let Some(shadowed_parameter_number) = shadowed_parameter_number {
					numbers.insert(parameter, shadowed_parameter_number);
				}

				if let Some(shadowed_fixpoint_number) = shadowed_fixpoint_number {
					numbers.insert(mu_binding, shadowed_fixpoint_number);
				}

				Some(BaseTerm::Function {
					fixpoint_name: Some(bound_fixpoint_number),
					parameter: bound_parameter_number,
					domain,
					codomain,
					body: Box::new(body),
				})
			} else {
				None
			}
		},
		(None, ParsedTerm::Application { function, argument }) => {
			let function = elaborate_term(context.clone(), *function, None, names, numbers, symbol_generator)?;
			if let BaseType::Power { domain, codomain } = function.ty() {
				let argument = elaborate_term(context, *argument, Some(*domain), names, numbers, symbol_generator)?;
				Some(BaseTerm::Application {
					ty: *codomain,
					function: Box::new(function),
					argument: Box::new(argument),
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
			let definition = elaborate_term(context.clone(), *definition, None, names, numbers, symbol_generator)?;

			let shadowed_assignee_number = numbers.get(&binding).copied();
			let [bound_assignee_number] = symbol_generator.fresh();
			names.insert(bound_assignee_number, binding.clone());
			numbers.insert(binding.clone(), bound_assignee_number);

			let rest = elaborate_term(
				context.extend(BaseVariable::Auto(bound_assignee_number), definition.ty()),
				*rest,
				None,
				names,
				numbers,
				symbol_generator,
			)?;

			if let Some(shadowed_assignee_number) = shadowed_assignee_number {
				numbers.insert(binding, shadowed_assignee_number);
			}

			Some(BaseTerm::Assignment {
				ty: rest.ty(),
				assignee: bound_assignee_number,
				definition: Box::new(definition),
				rest: Box::new(rest),
			})
		},
		(None, ParsedTerm::EqualityQuery { left, right }) => {
			let left = elaborate_term(context.clone(), *left, None, names, numbers, symbol_generator)?;
			let right = elaborate_term(context, *right, Some(left.ty()), names, numbers, symbol_generator)?;
			Some(BaseTerm::EqualityQuery {
				left: Box::new(left),
				right: Box::new(right),
			})
		},
		(None, ParsedTerm::CaseSplit { scrutinee, cases }) => {
			let scrutinee = elaborate_term(context.clone(), *scrutinee, None, names, numbers, symbol_generator)?;
			match_slice! {cases.cases.into_boxed_slice();
				[(case_0, body_0), (case_1, body_1)] => {
					// Ensure that the case split is exhaustive.
					if case_0 ^ case_1 {
						let body_0 = elaborate_term(context.clone(), *body_0, None, names, numbers, symbol_generator)?;
						let body_1 = elaborate_term(context, *body_1, Some(body_0.ty()), names, numbers, symbol_generator)?;
						Some(BaseTerm::CaseSplit {
							ty: body_0.ty(),
							scrutinee: Box::new(scrutinee),
							cases: vec![(case_0, Box::new(body_0)), (case_1, Box::new(body_1))],
						})
					} else {
						None
					}
				},
				_ => None,
			}
		},
		(Some(expected_ty), parsed_term) => elaborate_term(context, parsed_term, None, names, numbers, symbol_generator)
			.filter(|typed_term| typed_term.ty() == expected_ty),
	}
}

pub fn elaborate_program(
	parsed_term: ParsedTerm,
	symbol_generator: &mut LabelGenerator,
) -> Option<(BaseTerm, HashMap<Label, String>)> {
	let mut names = HashMap::new();
	let mut numbers = HashMap::new();

	let term = elaborate_term(
		Context::new(vec![
			(
				BaseVariable::Name("add".to_owned()),
				BaseType::Power {
					domain: Box::new(BaseType::Integer),
					codomain: Box::new(BaseType::Power {
						domain: Box::new(BaseType::Integer),
						codomain: Box::new(BaseType::Integer),
					}),
				},
			),
			(
				BaseVariable::Name("add2".to_owned()),
				BaseType::Power {
					domain: Box::new(BaseType::Product(Vec::from([BaseType::Integer, BaseType::Integer]))),
					codomain: Box::new(BaseType::Integer),
				},
			),
		]),
		parsed_term,
		None,
		&mut names,
		&mut numbers,
		symbol_generator,
	)?;

	Some((term, names))
}

use std::collections::HashMap;

use super::label::{Label, LabelGenerator};
use crate::{
	interpreter::base::{BaseIntrinsic, BaseTerm, BaseType, BaseVariable},
	parser::parser::*,
	utility::slice::match_slice,
};

#[derive(Clone)]
pub struct LoopTypes {
	domain: BaseType,
	codomain: BaseType,
}

#[derive(Clone)]
pub struct Context {
	tys: Vec<(BaseVariable, BaseType)>,
	loops: Vec<(Label, LoopTypes)>,
}

pub struct Renamer {
	names: HashMap<Label, String>,
	numbers: HashMap<String, Label>,
	loop_numbers: HashMap<String, Label>,
}

impl Renamer {
	pub fn new() -> Self {
		Self {
			names: HashMap::new(),
			numbers: HashMap::new(),
			loop_numbers: HashMap::new(),
		}
	}

	pub fn insert(&mut self, name: String, number: Label) -> Option<(String, Label)> {
		let shadow = self.get_label(&name).map(|label| (name.clone(), label));
		self.names.insert(number, name.clone());
		self.numbers.insert(name, number);
		shadow
	}

	pub fn unshadow(&mut self, shadow: Option<(String, Label)>) {
		if let Some((name, label)) = shadow {
			self.numbers.insert(name, label);
		}
	}

	pub fn insert_loop(&mut self, name: String, number: Label) {
		self.loop_numbers.insert(name, number);
	}

	pub fn get_label(&self, name: &String) -> Option<Label> {
		self.numbers.get(name).copied()
	}

	pub fn get_loop_label(&self, name: &String) -> Option<Label> {
		self.loop_numbers.get(name).copied()
	}
}

impl Context {
	pub fn new(tys: Vec<(BaseVariable, BaseType)>) -> Self {
		Self { tys, loops: vec![] }
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
				tys.push((name, ty));
				tys
			},
			loops: self.loops.clone(),
		}
	}

	pub fn clear_loops(&self) -> Self {
		Self {
			tys: self.tys.clone(),
			loops: Vec::new(),
		}
	}

	pub fn find_loop(&self, name: &Label) -> Option<LoopTypes> {
		for (test, ty) in self.loops.iter().rev() {
			if test == name {
				return Some(ty.clone());
			}
		}
		None
	}

	pub fn extend_loop(&self, label: Label, domain: BaseType, codomain: BaseType) -> Self {
		Self {
			tys: self.tys.clone(),
			loops: {
				let mut loops = self.loops.clone();
				loops.push((label, LoopTypes { domain, codomain }));
				loops
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
	renamer: &mut Renamer,
	symbol_generator: &mut LabelGenerator,
) -> Option<BaseTerm> {
	match (expected_ty, parsed_term) {
		(None, ParsedTerm::Polarity(pole)) => Some(BaseTerm::Polarity(pole)),
		(None, ParsedTerm::Integer(x)) => Some(BaseTerm::Integer(x)),
		(None, ParsedTerm::Name(name)) => {
			let variable = renamer
				.get_label(&name)
				.map_or(BaseVariable::Name(name), |number| BaseVariable::Auto(number));

			let ty = context.find(&variable)?;

			Some(BaseTerm::Name(ty, variable))
		},
		(None, ParsedTerm::Tuple(tuple)) => {
			let typed_terms = tuple
				.into_iter()
				.map(move |parsed_term| elaborate_term(context.clone(), parsed_term, None, renamer, symbol_generator))
				.collect::<Option<Vec<_>>>()
				.map(|v| {
					v.into_iter()
						.map(|expression| (expression.ty(), expression.clone()))
						.collect()
				})?;

			Some(BaseTerm::Tuple(typed_terms))
		},
		(None, ParsedTerm::Projection { tuple, index }) => {
			let tuple = elaborate_term(context, *tuple, None, renamer, symbol_generator)?;
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
			let codomain = if let Some(codomain) = codomain {
				Some(elaborate_ty(codomain)?)
			} else {
				None
			};

			let [bound_parameter_number] = symbol_generator.fresh();
			let parameter_shadow = renamer.insert(parameter.clone(), bound_parameter_number);

			let body = elaborate_term(
				context
					.clear_loops()
					.extend(BaseVariable::Auto(bound_parameter_number), domain.clone()),
				*body,
				codomain.clone(),
				renamer,
				symbol_generator,
			)?;

			let codomain = body.ty();

			renamer.unshadow(parameter_shadow);

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
				let codomain = elaborate_ty(codomain?)?;

				let [bound_fixpoint_number] = symbol_generator.fresh();
				let mu_shadow = renamer.insert(mu_binding.clone(), bound_fixpoint_number);

				let [bound_parameter_number] = symbol_generator.fresh();
				let parameter_shadow = renamer.insert(parameter.clone(), bound_parameter_number);

				let body = elaborate_term(
					context
						.clear_loops()
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
					renamer,
					symbol_generator,
				)?;

				renamer.unshadow(parameter_shadow);
				renamer.unshadow(mu_shadow);

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
			let function = elaborate_term(context.clone(), *function, None, renamer, symbol_generator)?;
			if let BaseType::Power { domain, codomain } = function.ty() {
				let argument = elaborate_term(context, *argument, Some(*domain), renamer, symbol_generator)?;
				Some(BaseTerm::Application {
					codomain: *codomain,
					function: Box::new(function),
					argument: Box::new(argument),
				})
			} else {
				None
			}
		},
		(None, ParsedTerm::IntrinsicInvocation { intrinsic, arguments }) => match intrinsic.as_str() {
			"add" => {
				match_slice! { arguments.into_boxed_slice();
					[term_0, term_1] => {
						let term_0 = elaborate_term(context.clone(), term_0, Some(BaseType::Integer), renamer, symbol_generator)?;
						let term_1 = elaborate_term(context, term_1, Some(BaseType::Integer), renamer, symbol_generator)?;
						Some(BaseTerm::IntrinsicInvocation { intrinsic: BaseIntrinsic::Add, arguments: vec![term_0, term_1] })
					},
					_ => None,
				}
			},
			_ => None,
		},
		(
			None,
			ParsedTerm::Assignment {
				binding,
				definition,
				rest,
			},
		) => {
			let definition = elaborate_term(context.clone(), *definition, None, renamer, symbol_generator)?;

			let [bound_assignee_number] = symbol_generator.fresh();
			let assignee_shadow = renamer.insert(binding.clone(), bound_assignee_number);

			let rest = elaborate_term(
				context.extend(BaseVariable::Auto(bound_assignee_number), definition.ty()),
				*rest,
				None,
				renamer,
				symbol_generator,
			)?;

			renamer.unshadow(assignee_shadow);

			Some(BaseTerm::Assignment {
				ty: rest.ty(),
				assignee: bound_assignee_number,
				definition: Box::new(definition),
				rest: Box::new(rest),
			})
		},
		(None, ParsedTerm::EqualityQuery { left, right }) => {
			let left = elaborate_term(context.clone(), *left, None, renamer, symbol_generator)?;
			let ty = left.ty();
			let right = elaborate_term(context, *right, Some(ty.clone()), renamer, symbol_generator)?;
			Some(BaseTerm::EqualityQuery {
				ty,
				left: Box::new(left),
				right: Box::new(right),
			})
		},
		(None, ParsedTerm::CaseSplit { scrutinee, cases }) => {
			let scrutinee = elaborate_term(context.clone(), *scrutinee, None, renamer, symbol_generator)?;
			match_slice! {cases.cases.into_boxed_slice();
				[(case_0, body_0), (case_1, body_1)] => {
					// Ensure that the case split is exhaustive.
					if case_0 ^ case_1 {
						let body_0 = elaborate_term(context.clone(), *body_0, None, renamer, symbol_generator)?;
						let body_1 = elaborate_term(context, *body_1, Some(body_0.ty()), renamer, symbol_generator)?;
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
		(
			None,
			ParsedTerm::Loop {
				loop_name,
				argument,
				parameter,
				codomain,
				body,
			},
		) => {
			let codomain = elaborate_ty(codomain)?;

			let argument = elaborate_term(context.clone(), *argument, None, renamer, symbol_generator)?;

			let domain = argument.ty();

			let [bound_loop_number] = symbol_generator.fresh();
			renamer.insert_loop(loop_name.clone(), bound_loop_number);

			let [bound_parameter_number] = symbol_generator.fresh();
			let parameter_shadow = renamer.insert(parameter.clone(), bound_parameter_number);

			let body_context = context
				.extend(BaseVariable::Auto(bound_parameter_number), domain.clone())
				.extend_loop(bound_loop_number, domain, codomain.clone());

			let body = elaborate_term(body_context, *body, Some(BaseType::Empty), renamer, symbol_generator)?;

			renamer.unshadow(parameter_shadow);

			Some(BaseTerm::Loop {
				codomain,
				loop_name: bound_loop_number,
				parameter: bound_parameter_number,
				argument: Box::new(argument),
				body: Box::new(body),
			})
		},
		(None, ParsedTerm::Step { loop_name, argument }) => {
			let loop_name = renamer.get_loop_label(&loop_name)?;
			let domain = context.find_loop(&loop_name)?.domain;
			let argument = elaborate_term(context.clone(), *argument, Some(domain), renamer, symbol_generator)?;
			Some(BaseTerm::Step {
				loop_name,
				argument: Box::new(argument),
			})
		},
		(None, ParsedTerm::Emit { loop_name, argument }) => {
			let loop_name = renamer.get_loop_label(&loop_name)?;
			let codomain = context.find_loop(&loop_name)?.codomain;
			let argument = elaborate_term(context.clone(), *argument, Some(codomain), renamer, symbol_generator)?;
			Some(BaseTerm::Emit {
				loop_name,
				argument: Box::new(argument),
			})
		},
		(Some(expected_ty), parsed_term) => elaborate_term(context, parsed_term, None, renamer, symbol_generator)
			.filter(|typed_term| typed_term.ty() == expected_ty),
	}
}

pub fn elaborate_program(parsed_term: ParsedTerm, symbol_generator: &mut LabelGenerator) -> Option<BaseTerm> {
	let mut renamer = Renamer::new();
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
		&mut renamer,
		symbol_generator,
	)?;

	Some(term)
}

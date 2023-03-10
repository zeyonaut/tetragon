use std::sync::Arc;

use super::elaborator::*;
use crate::interpreter::cypress::*;

pub struct SymbolGenerator(u64);

impl SymbolGenerator {
	pub fn fresh(&mut self) -> u64 {
		let symbol = self.0;
		self.0 += 1;
		symbol
	}
}

pub fn convert_type_to_cps(base_ty: BaseType) -> CypressType {
	match base_ty {
		BaseType::Polarity => CypressType::Polarity,
		BaseType::Integer => CypressType::Integer,
		BaseType::Power { domain, codomain } => CypressType::Power {
			domain: Box::new(convert_type_to_cps((*domain).clone())),
			codomain: Box::new(convert_type_to_cps(*codomain)),
		},
		BaseType::Product(_) => unimplemented!(),
	}
}

pub fn convert_expression_to_cps(
	base_expression: BaseExpression,
	// A 'one-hole context' which a variable can be plugged into.
	translation_context: Arc<dyn Fn(CypressVariable, &mut SymbolGenerator) -> Option<CypressTerm>>,
	symbol_generator: &mut SymbolGenerator,
) -> Option<CypressTerm> {
	let ty = base_expression.ty;
	match base_expression.term {
		BaseTerm::Polarity(x) => {
			let binding = CypressVariable::Auto(symbol_generator.fresh());
			Some(CypressTerm::AssignValue {
				binding: binding.clone(),
				ty: CypressType::Polarity,
				value: CypressValue::Polarity(x),
				rest: Box::new(translation_context(binding, symbol_generator)?),
			})
		},
		BaseTerm::Integer(x) => {
			let binding = CypressVariable::Auto(symbol_generator.fresh());
			Some(CypressTerm::AssignValue {
				binding: binding.clone(),
				ty: CypressType::Integer,
				value: CypressValue::Integer(x),
				rest: Box::new(translation_context(binding, symbol_generator)?),
			})
		},
		BaseTerm::Name(x) => {
			// TODO: Does it matter that this is not necessarily fresh?
			Some(translation_context(CypressVariable::Name(x), symbol_generator)?)
		},
		BaseTerm::Tuple(_) => unimplemented!(),
		BaseTerm::Projection { tuple: _, index: _ } => unimplemented!(),
		BaseTerm::Function {
			fixpoint_name,
			parameter,
			domain,
			codomain,
			body,
		} => {
			let binding = CypressVariable::Auto(symbol_generator.fresh());
			let continuation = CypressLabel(symbol_generator.fresh());
			let parameter = CypressVariable::Name(parameter);

			Some(CypressTerm::DeclareFunction {
				fixpoint_name,
				binding: binding.clone(),
				domain: convert_type_to_cps(domain),
				codomain: convert_type_to_cps(codomain),
				continuation,
				parameter,
				body: Box::new(convert_expression_to_cps(
					*body,
					Arc::new(move |argument, _| Some(CypressTerm::Continue { continuation, argument })),
					symbol_generator,
				)?),
				rest: Box::new(translation_context(binding, symbol_generator)?),
			})
		},
		BaseTerm::Application { function, argument } => {
			// TODO: Handle intrinsic functions as operations instead. Maybe? Or how long can I delay the introduction of intrinsics?
			let continuation = CypressLabel(symbol_generator.fresh());
			let outcome = CypressVariable::Auto(symbol_generator.fresh());

			match convert_type_to_cps(function.ty.clone()) {
				CypressType::Power { domain: _, codomain } => Some(convert_expression_to_cps(
					*function,
					Arc::new(move |function, symbol_generator| {
						let (codomain, outcome, translation_context) =
							((*codomain).clone(), outcome.clone(), translation_context.clone());
						convert_expression_to_cps(
							(*argument).clone(),
							Arc::new(move |argument, symbol_generator| {
								Some(CypressTerm::DeclareContinuation {
									label: continuation,
									domain: codomain.clone(),
									parameter: outcome.clone(),
									body: Box::new(translation_context(outcome.clone(), symbol_generator)?),
									rest: Box::new(CypressTerm::Apply {
										function: function.clone(),
										continuation,
										argument,
									}),
								})
							}),
							symbol_generator,
						)
					}),
					symbol_generator,
				)?),
				_ => None,
			}
		},
		BaseTerm::Assignment {
			assignee,
			definition,
			rest,
		} => {
			let continuation = CypressLabel(symbol_generator.fresh());
			Some(CypressTerm::DeclareContinuation {
				label: continuation,
				domain: convert_type_to_cps(definition.ty.clone()),
				parameter: CypressVariable::Name(assignee),
				body: Box::new(convert_expression_to_cps(*rest, translation_context, symbol_generator)?),
				rest: Box::new(convert_expression_to_cps(
					*definition,
					Arc::new(move |variable, _| {
						Some(CypressTerm::Continue {
							continuation,
							argument: variable,
						})
					}),
					symbol_generator,
				)?),
			})
		},
		BaseTerm::EqualityQuery { left, right } => {
			let binding = CypressVariable::Auto(symbol_generator.fresh());
			convert_expression_to_cps(
				*left,
				Arc::new(move |left, symbol_generator| {
					let (binding, translation_context) = (binding.clone(), translation_context.clone());
					Some(convert_expression_to_cps(
						(*right).clone(),
						Arc::new(move |right, symbol_generator| {
							Some(CypressTerm::AssignOperation {
								binding: binding.clone(),
								ty: CypressType::Polarity,
								operation: CypressOperation::EqualsQuery([left.clone(), right]),
								rest: Box::new(translation_context(binding.clone(), symbol_generator)?),
							})
						}),
						symbol_generator,
					)?)
				}),
				symbol_generator,
			)
		},
		BaseTerm::CaseSplit { scrutinee, cases } => {
			let outcome_continuation = CypressLabel(symbol_generator.fresh());
			let outcome_parameter = CypressVariable::Auto(symbol_generator.fresh());
			let yes_continuation = CypressLabel(symbol_generator.fresh());
			let yes_parameter = CypressVariable::Auto(symbol_generator.fresh());
			let no_continuation = CypressLabel(symbol_generator.fresh());
			let no_parameter = CypressVariable::Auto(symbol_generator.fresh());
			let outcome_ty = convert_type_to_cps(ty);

			let mut yes_term = None;
			let mut no_term = None;
			for (pattern, body) in cases {
				if pattern {
					yes_term = Some(*body);
				} else {
					no_term = Some(*body);
				}
			}
			let yes_term = yes_term?;
			let no_term = no_term?;

			Some(CypressTerm::DeclareContinuation {
				label: outcome_continuation,
				domain: outcome_ty,
				parameter: outcome_parameter.clone(),
				body: Box::new(translation_context(outcome_parameter, symbol_generator)?),
				rest: Box::new(CypressTerm::DeclareContinuation {
					label: yes_continuation,
					domain: CypressType::Unity,
					parameter: yes_parameter,
					body: Box::new(convert_expression_to_cps(
						yes_term,
						Arc::new(move |variable, _| {
							Some(CypressTerm::Continue {
								continuation: outcome_continuation,
								argument: variable,
							})
						}),
						symbol_generator,
					)?),
					rest: Box::new(CypressTerm::DeclareContinuation {
						label: no_continuation,
						domain: CypressType::Unity,
						parameter: no_parameter,
						body: Box::new(convert_expression_to_cps(
							no_term,
							Arc::new(move |variable, _| {
								Some(CypressTerm::Continue {
									continuation: outcome_continuation,
									argument: variable,
								})
							}),
							symbol_generator,
						)?),
						rest: Box::new(convert_expression_to_cps(
							*scrutinee,
							Arc::new(move |variable, _| {
								Some(CypressTerm::CaseSplit {
									scrutinee: variable,
									yes_continuation,
									no_continuation,
								})
							}),
							symbol_generator,
						)?),
					}),
				}),
			})
		},
	}
}

pub fn convert_program_to_cps(base_expression: BaseExpression) -> Option<CypressTerm> {
	let mut symbol_generator = SymbolGenerator(0);

	convert_expression_to_cps(
		base_expression,
		Arc::new(|variable, _| Some(CypressTerm::Halt { argument: variable })),
		&mut symbol_generator,
	)
}

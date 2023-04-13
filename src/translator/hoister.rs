use std::collections::HashMap;

use super::label::{Label, LabelGenerator};
use crate::{
	interpreter::{
		cypress::{
			CypressOperation, CypressPrimitive, CypressProjection, CypressProjector, CypressTerm, CypressType, CypressVariable,
		},
		firefly::{
			BinaryOperator, FireflyOperand, FireflyOperation, FireflyPrimitive, FireflyProcedure, FireflyProgram,
			FireflyProjection, FireflyProjector, FireflyStatement, FireflyTerm, FireflyTerminator, FireflyType,
		},
	},
	utility::ignore::Ignore,
};

struct Substitution(HashMap<Label, FireflyProjection>);

trait Substitute {
	fn apply(&mut self, substitution: &Substitution);

	fn subbing(mut self, substitution: &Substitution) -> Self
	where
		Self: Sized,
	{
		self.apply(substitution);
		self
	}
}

impl Substitute for FireflyProjection {
	fn apply(&mut self, substitution: &Substitution) {
		if let CypressVariable::Local(local) = self.root {
			if let Some(mut substituend) = substitution.0.get(&local).cloned() {
				substituend.projectors.append(&mut self.projectors);
				*self = substituend;
			}
		}
	}
}

impl Substitute for FireflyOperand {
	fn apply(&mut self, substitution: &Substitution) {
		match self {
			FireflyOperand::Copy(projection) => projection.apply(substitution),
			FireflyOperand::Constant(_) => (),
		}
	}
}

impl Substitute for FireflyOperation {
	fn apply(&mut self, substitution: &Substitution) {
		match self {
			FireflyOperation::Address(projection) => projection.apply(substitution),
			FireflyOperation::Id(_, operands) => operands.apply(substitution),
			FireflyOperation::Binary(_, operands) => operands.iter_mut().map(|x| x.apply(substitution)).collect(),
			FireflyOperation::Pair(operands) => operands.iter_mut().map(|(_, operand)| operand.apply(substitution)).collect(),
			FireflyOperation::Closure(procedure, snapshot) => {
				procedure.apply(substitution);
				snapshot.iter_mut().map(|(_, x)| x.apply(substitution)).collect()
			},
		}
	}
}

impl core::ops::Mul<Self> for Substitution {
	type Output = Self;

	fn mul(mut self, other: Self) -> Self::Output {
		for substituend in self.0.values_mut() {
			substituend.apply(&other)
		}

		for (replacee, substituend) in other.0 {
			self.0.entry(replacee).or_insert(substituend);
		}

		self
	}
}

impl Substitute for FireflyTerm {
	fn apply(&mut self, substitution: &Substitution) {
		for statement in &mut self.statements {
			match statement {
				FireflyStatement::Assign { binding: _, operation } => operation.apply(substitution),
				// Because every parameter is fresh, we are not concerned about shadowing.
				FireflyStatement::DeclareContinuation {
					label: _,
					parameter: _,
					domain: _,
					body,
				} => body.apply(substitution),
			}
		}

		match &mut self.terminator {
			FireflyTerminator::Branch {
				scrutinee,
				yes_continuation: _,
				no_continuation: _,
			} => scrutinee.apply(substitution),
			FireflyTerminator::Apply {
				procedure,
				domain: _,
				codomain: _,
				snapshot,
				continuation_label: _,
				argument,
			} => [procedure, snapshot, argument].map(|x| x.apply(substitution)).ignore(),
			FireflyTerminator::Jump {
				continuation_label: _,
				domain: _,
				argument,
			} => argument.apply(substitution),
		}
	}
}

fn get_if_local(projection: &CypressProjection) -> Option<Label> {
	if let CypressVariable::Local(label) = projection.root {
		Some(label.clone())
	} else {
		None
	}
}

pub fn compute_free_variables_in_operation(operation: &CypressOperation) -> HashMap<Label, CypressType> {
	match operation {
		CypressOperation::Id(ty, x) => [x].into_iter().filter_map(get_if_local).map(|x| (x, ty.clone())).collect(),
		CypressOperation::EqualsQuery(ty, x) => x.into_iter().filter_map(get_if_local).map(|x| (x, ty.clone())).collect(),
		CypressOperation::Add(x) => x
			.into_iter()
			.filter_map(get_if_local)
			.map(|x| (x, CypressType::Integer))
			.collect(),
		CypressOperation::Pair(vs) => (*vs)
			.into_iter()
			.filter_map(|(ty, x)| get_if_local(x).map(|x| (x, ty.clone())))
			.collect(),
	}
}

pub fn compute_free_variables_in_term(term: &CypressTerm) -> HashMap<Label, CypressType> {
	match term {
		CypressTerm::AssignValue {
			binding,
			ty: _,
			value: _,
			rest,
		} => {
			let mut free_variables = compute_free_variables_in_term(&*rest);
			free_variables.remove(&binding);
			free_variables
		},
		CypressTerm::AssignOperation {
			binding,
			operation,
			rest,
		} => {
			let mut free_variables = compute_free_variables_in_term(&*rest);
			free_variables.remove(&binding);
			free_variables.extend(compute_free_variables_in_operation(operation));
			free_variables
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
			let mut body_free_variables = compute_free_variables_in_term(&*body);
			body_free_variables.remove(&parameter);
			if let Some(fixpoint_name) = fixpoint_name {
				body_free_variables.remove(&fixpoint_name);
			};
			body_free_variables.extend(compute_free_variables_in_term(&*rest));
			body_free_variables.remove(&binding);
			body_free_variables
		},
		CypressTerm::DeclareContinuation {
			label: _,
			domain: _,
			parameter,
			body,
			rest,
		} => {
			let mut body_free_variables = compute_free_variables_in_term(&*body);
			body_free_variables.remove(&parameter);
			body_free_variables.extend(compute_free_variables_in_term(&*rest));
			body_free_variables
		},
		CypressTerm::CaseSplit {
			scrutinee,
			yes_continuation: _,
			no_continuation: _,
		} => [scrutinee]
			.into_iter()
			.filter_map(get_if_local)
			.map(|x| (x, CypressType::Polarity))
			.collect(),
		CypressTerm::Apply {
			function,
			domain,
			codomain,
			continuation: _,
			argument,
		} => [
			(
				function,
				CypressType::Power {
					domain: Box::new(domain.clone()),
					codomain: Box::new(codomain.clone()),
				},
			),
			(argument, domain.clone()),
		]
		.into_iter()
		.filter_map(|(x, ty)| get_if_local(x).map(|x| (x, ty)))
		.collect(),
		CypressTerm::Continue {
			continuation_label: _,
			argument,
			domain,
		} => [argument]
			.into_iter()
			.filter_map(get_if_local)
			.map(|x| (x, domain.clone()))
			.collect(),
	}
}

pub fn hoist_projection(projection: CypressProjection) -> FireflyProjection {
	FireflyProjection {
		root: projection.root,
		projectors: projection
			.projectors
			.into_iter()
			.map(|x| match x {
				CypressProjector::Field(x) => FireflyProjector::Field(x),
			})
			.collect(),
	}
}

pub fn hoist_primitive(value: CypressPrimitive) -> FireflyPrimitive {
	match value {
		CypressPrimitive::Unity => FireflyPrimitive::Unity,
		CypressPrimitive::Polarity(x) => FireflyPrimitive::Polarity(x),
		CypressPrimitive::Integer(x) => FireflyPrimitive::Integer(x),
	}
}

pub fn hoist_operation(operation: CypressOperation) -> FireflyOperation {
	match operation {
		CypressOperation::Id(ty, x) => FireflyOperation::Id(hoist_ty(ty), FireflyOperand::Copy(hoist_projection(x))),
		CypressOperation::EqualsQuery(ty, x) => FireflyOperation::Binary(
			BinaryOperator::EqualsQuery(hoist_ty(ty)),
			x.map(|x| FireflyOperand::Copy(hoist_projection(x))),
		),
		CypressOperation::Add(x) => {
			FireflyOperation::Binary(BinaryOperator::Add, x.map(|x| FireflyOperand::Copy(hoist_projection(x))))
		},
		CypressOperation::Pair(x) => FireflyOperation::Pair(
			x.into_vec()
				.into_iter()
				.map(|(ty, projection)| (hoist_ty(ty), FireflyOperand::Copy(hoist_projection(projection))))
				.collect::<Vec<_>>()
				.into_boxed_slice(),
		),
	}
}

pub fn hoist_ty(ty: CypressType) -> FireflyType {
	match ty {
		CypressType::Unity => FireflyType::Unity,
		CypressType::Polarity => FireflyType::Polarity,
		CypressType::Integer => FireflyType::Integer,
		CypressType::Power { domain: _, codomain: _ } => FireflyType::Closure,
		CypressType::Product(factors) => FireflyType::Product(
			factors
				.into_vec()
				.into_iter()
				.map(hoist_ty)
				.collect::<Vec<_>>()
				.into_boxed_slice(),
		),
	}
}

pub fn hoist_term(
	term: CypressTerm,
	procedures: &mut HashMap<Label, FireflyProcedure>,
	symbol_generator: &mut LabelGenerator,
) -> FireflyTerm {
	match term {
		CypressTerm::AssignValue {
			binding,
			ty,
			value,
			rest,
		} => {
			let mut rest = hoist_term(*rest, procedures, symbol_generator);
			rest.statements.push(FireflyStatement::Assign {
				binding,
				operation: FireflyOperation::Id(hoist_ty(ty), FireflyOperand::Constant(hoist_primitive(value))),
			});
			rest
		},
		CypressTerm::AssignOperation {
			binding,
			operation,
			rest,
		} => {
			let mut rest = hoist_term(*rest, procedures, symbol_generator);
			rest.statements.push(FireflyStatement::Assign {
				binding,
				operation: hoist_operation(operation),
			});
			rest
		},
		CypressTerm::DeclareFunction {
			binding,
			fixpoint_name,
			domain,
			codomain,
			parameter,
			body,
			rest,
		} => {
			let [procedure_label, environment] = symbol_generator.fresh();

			let free_variables = {
				let mut free_variables = compute_free_variables_in_term(&body);
				free_variables.remove(&parameter);
				if let Some(fixpoint_name) = fixpoint_name {
					free_variables.remove(&fixpoint_name);
				}
				free_variables.into_iter().collect::<Vec<_>>()
			};

			// Generate a procedure.
			{
				let substitution = Substitution({
					let mut mapping = free_variables
						.iter()
						.cloned()
						.enumerate()
						.map(|(i, (variable, _))| {
							(
								variable,
								FireflyProjection::new(CypressVariable::Local(environment)).project(FireflyProjector::Free(i)),
							)
						})
						.collect::<HashMap<_, _>>();
					mapping.insert(
						parameter,
						FireflyProjection::new(CypressVariable::Local(parameter)).project(FireflyProjector::Parameter),
					);
					mapping
				});

				let mut body = hoist_term(*body, procedures, symbol_generator).subbing(&substitution);

				if let Some(fixpoint_name) = fixpoint_name {
					body.statements.push(FireflyStatement::Assign {
						binding: fixpoint_name,
						operation: FireflyOperation::Closure(
							FireflyOperand::Constant(FireflyPrimitive::Procedure(procedure_label)),
							free_variables
								.iter()
								.enumerate()
								.map(|(i, (_, ty))| {
									(
										hoist_ty(ty.clone()),
										FireflyOperand::Copy(
											FireflyProjection::new(CypressVariable::Local(environment))
												.project(FireflyProjector::Free(i)),
										),
									)
								})
								.collect::<Vec<_>>()
								.into_boxed_slice(),
						),
					});
				}

				procedures.insert(
					procedure_label,
					FireflyProcedure {
						capture: Some((
							environment,
							free_variables.iter().map(|(_, ty)| hoist_ty(ty.clone())).collect(),
						)),
						parameter: Some(parameter),
						domain: hoist_ty(domain),
						codomain: hoist_ty(codomain),
						body,
					},
				);
			}

			// Generate and return a closure assignment.
			{
				let captures = free_variables
					.into_iter()
					.map(|(variable, ty)| {
						(
							hoist_ty(ty),
							FireflyOperand::Copy(FireflyProjection::new(CypressVariable::Local(variable))),
						)
					})
					.collect::<Vec<_>>()
					.into_boxed_slice();

				let mut rest = hoist_term(*rest, procedures, symbol_generator);

				rest.statements.push(FireflyStatement::Assign {
					binding,
					operation: FireflyOperation::Closure(
						FireflyOperand::Constant(FireflyPrimitive::Procedure(procedure_label)),
						captures,
					),
				});

				rest
			}
		},
		CypressTerm::DeclareContinuation {
			label,
			domain,
			parameter,
			body,
			rest,
		} => {
			let mut rest = hoist_term(*rest, procedures, symbol_generator);
			rest.statements.push(FireflyStatement::DeclareContinuation {
				label,
				parameter,
				domain: hoist_ty(domain),
				body: hoist_term(*body, procedures, symbol_generator),
			});
			rest
		},
		CypressTerm::CaseSplit {
			scrutinee,
			yes_continuation,
			no_continuation,
		} => FireflyTerm::new(FireflyTerminator::Branch {
			scrutinee: FireflyOperand::Copy(hoist_projection(scrutinee)),
			yes_continuation: yes_continuation,
			no_continuation: no_continuation,
		}),
		CypressTerm::Apply {
			function,
			domain,
			codomain,
			continuation,
			argument,
		} => {
			let function_projection = hoist_projection(function);
			FireflyTerm::new(FireflyTerminator::Apply {
				procedure: FireflyOperand::Copy(function_projection.clone().project(FireflyProjector::Procedure)),
				domain: hoist_ty(domain),
				codomain: hoist_ty(codomain),
				snapshot: FireflyOperand::Copy(function_projection.project(FireflyProjector::Snapshot)),
				continuation_label: continuation,
				argument: FireflyOperand::Copy(hoist_projection(argument)),
			})
		},
		CypressTerm::Continue {
			domain,
			continuation_label,
			argument,
		} => FireflyTerm::new(FireflyTerminator::Jump {
			continuation_label,
			domain: hoist_ty(domain),
			argument: FireflyOperand::Copy(hoist_projection(argument)),
		}),
	}
}

// Closure conversion turns functions, which may have free variables, into closures, which bundle a procedure label and an environment.
// All nested function declarations are hoisted to the top level of the program as first-order procedures.
pub fn hoist_program(term: CypressTerm, ty: CypressType, symbol_generator: &mut LabelGenerator) -> FireflyProgram {
	let mut procedures = HashMap::<Label, FireflyProcedure>::new();

	//let codomain = hoist_ty(term.ty)
	let entry_body = hoist_term(term, &mut procedures, symbol_generator);

	let [entry] = symbol_generator.fresh();
	procedures.insert(
		entry,
		FireflyProcedure {
			capture: None,
			parameter: None,
			domain: FireflyType::Unity,
			codomain: hoist_ty(ty),
			body: entry_body,
		},
	);

	FireflyProgram {
		procedures,
		entry,
		symbol_generator: symbol_generator.clone(),
	}
}

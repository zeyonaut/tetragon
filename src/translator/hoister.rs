use std::collections::HashMap;

use super::label::{Label, LabelGenerator};
use crate::interpreter::{
	base::{BaseIntrinsic, BaseTerm, BaseType, BaseVariable},
	june::{JuneIntrinsic, JunePrimitive, JuneProcedure, JuneProgram, JuneTerm, JuneType},
};

pub fn hoist(term: BaseTerm, mut symbol_generator: LabelGenerator) -> JuneProgram {
	let mut procedures = HashMap::<Label, JuneProcedure>::new();

	let entry_term = hoist_term(term, &mut procedures, &mut symbol_generator);
	let [entry] = symbol_generator.fresh();
	procedures.insert(
		entry,
		JuneProcedure {
			domain: JuneType::Unity,
			parameter: None,
			capture: None,
			body: entry_term,
		},
	);

	JuneProgram {
		procedures,
		entry,
		symbol_generator,
	}
}

fn hoist_term(
	term: BaseTerm,
	procedures: &mut HashMap<Label, JuneProcedure>,
	symbol_generator: &mut LabelGenerator,
) -> JuneTerm {
	match term {
		BaseTerm::Polarity(x) => JuneTerm::Primitive(JunePrimitive::Polarity(x)),
		BaseTerm::Integer(x) => JuneTerm::Primitive(JunePrimitive::Integer(x)),
		BaseTerm::Name(ty, name) => JuneTerm::Name(hoist_ty(ty), name),
		BaseTerm::Tuple(typed_fields) => JuneTerm::Tuple(
			typed_fields
				.into_iter()
				.map(|(factor, field)| (hoist_ty(factor), hoist_term(field, procedures, symbol_generator)))
				.collect(),
		),
		BaseTerm::Projection { ty, tuple, index } => JuneTerm::Projection {
			ty: hoist_ty(ty),
			tuple: Box::new(hoist_term(*tuple, procedures, symbol_generator)),
			index,
		},
		BaseTerm::Function {
			domain,
			codomain,
			fixpoint_name,
			parameter,
			body,
		} => {
			let domain = hoist_ty(domain);
			let codomain = hoist_ty(codomain);
			let [procedure_label] = symbol_generator.fresh();

			// Compute the free variables of the function.
			let function_upvars = {
				let mut function_upvars = compute_upvars(&body);
				function_upvars.remove(&parameter);
				if let Some(fixpoint_name) = &fixpoint_name {
					function_upvars.remove(fixpoint_name);
				}
				function_upvars.into_iter().collect::<Vec<_>>()
			};

			let upvar_tys = function_upvars.iter().map(|(_, ty)| hoist_ty(ty.clone())).collect::<Vec<_>>();

			// Insert a procedure.
			{
				let [snapshot_label] = symbol_generator.fresh();

				let substitution = Substitution(
					function_upvars
						.iter()
						.enumerate()
						.map(|(i, (variable, ty))| {
							(
								variable.clone(),
								JuneTerm::Free {
									ty: hoist_ty(ty.clone()),
									share: Box::new(JuneTerm::Name(
										JuneType::Share(Some(upvar_tys.clone())),
										BaseVariable::Auto(snapshot_label),
									)),
									index: i,
								},
							)
						})
						.collect::<HashMap<_, _>>(),
				);

				let mut body = hoist_term(*body, procedures, symbol_generator);

				substitute(&mut body, &substitution);

				if let Some(fixpoint_name) = fixpoint_name {
					body = JuneTerm::Assignment {
						ty: body.ty(),
						assignee: fixpoint_name,
						definition: Box::new(JuneTerm::Closure {
							domain: domain.clone(),
							codomain: codomain.clone(),
							procedure: procedure_label,
							fields: function_upvars
								.iter()
								.enumerate()
								.map(|(i, (_, ty))| JuneTerm::Free {
									ty: hoist_ty(ty.clone()),
									share: Box::new(JuneTerm::Name(
										JuneType::Share(Some(upvar_tys.clone())),
										BaseVariable::Auto(snapshot_label),
									)),
									index: i,
								})
								.collect(),
						}),
						rest: Box::new(body),
					}
				}

				procedures.insert(
					procedure_label,
					JuneProcedure {
						domain: domain.clone(),
						parameter: Some(parameter),
						capture: Some((snapshot_label, upvar_tys.clone())),
						body,
					},
				);
			}

			// Produce a tuple of the procedure and a snapshot of the required upvars.
			JuneTerm::Closure {
				domain,
				codomain,
				procedure: procedure_label,
				fields: function_upvars
					.into_iter()
					.map(|(var, ty)| JuneTerm::Name(hoist_ty(ty), BaseVariable::Auto(var)))
					.collect(),
			}
		},
		BaseTerm::Application {
			codomain,
			function,
			argument,
		} => JuneTerm::Application {
			codomain: hoist_ty(codomain),
			function: Box::new(hoist_term(*function, procedures, symbol_generator)),
			argument: Box::new(hoist_term(*argument, procedures, symbol_generator)),
		},
		BaseTerm::IntrinsicInvocation { intrinsic, arguments } => JuneTerm::IntrinsicInvocation {
			intrinsic: hoist_intrinsic(intrinsic),
			arguments: arguments
				.into_iter()
				.map(|argument| hoist_term(argument, procedures, symbol_generator))
				.collect(),
		},
		BaseTerm::Assignment {
			ty,
			assignee,
			definition,
			rest,
		} => JuneTerm::Assignment {
			ty: hoist_ty(ty),
			assignee: assignee,
			definition: Box::new(hoist_term(*definition, procedures, symbol_generator)),
			rest: Box::new(hoist_term(*rest, procedures, symbol_generator)),
		},
		BaseTerm::EqualityQuery { ty, left, right } => JuneTerm::EqualityQuery {
			ty: hoist_ty(ty),
			left: Box::new(hoist_term(*left, procedures, symbol_generator)),
			right: Box::new(hoist_term(*right, procedures, symbol_generator)),
		},
		BaseTerm::CaseSplit { ty, scrutinee, cases } => JuneTerm::CaseSplit {
			ty: hoist_ty(ty),
			scrutinee: Box::new(hoist_term(*scrutinee, procedures, symbol_generator)),
			cases: cases
				.into_iter()
				.map(|(case, term)| (case, Box::new(hoist_term(*term, procedures, symbol_generator))))
				.collect(),
		},
		BaseTerm::Loop {
			codomain,
			loop_name,
			parameter,
			argument,
			body,
		} => JuneTerm::Loop {
			codomain: hoist_ty(codomain),
			loop_name,
			parameter,
			argument: Box::new(hoist_term(*argument, procedures, symbol_generator)),
			body: Box::new(hoist_term(*body, procedures, symbol_generator)),
		},
		BaseTerm::Step { loop_name, argument } => JuneTerm::Step {
			loop_name,
			argument: Box::new(hoist_term(*argument, procedures, symbol_generator)),
		},
		BaseTerm::Emit { loop_name, argument } => JuneTerm::Emit {
			loop_name,
			argument: Box::new(hoist_term(*argument, procedures, symbol_generator)),
		},
	}
}

fn hoist_intrinsic(intrinsic: BaseIntrinsic) -> JuneIntrinsic {
	match intrinsic {
		BaseIntrinsic::Add => JuneIntrinsic::Add,
	}
}

fn hoist_ty(ty: BaseType) -> JuneType {
	match ty {
		BaseType::Empty => JuneType::Empty,
		BaseType::Polarity => JuneType::Polarity,
		BaseType::Integer => JuneType::Integer,
		BaseType::Product(factors) => JuneType::Product(factors.into_iter().map(hoist_ty).collect()),
		BaseType::Power { domain, codomain } => JuneType::Product(vec![
			JuneType::Procedure {
				domain: Box::new(hoist_ty(*domain)),
				codomain: Box::new(hoist_ty(*codomain)),
			},
			JuneType::Share(None),
		]),
	}
}

fn compute_upvars(term: &BaseTerm) -> HashMap<Label, BaseType> {
	use BaseTerm::*;
	match term {
		Polarity(_) | Integer(_) => HashMap::new(),
		Name(ty, name) => match name {
			BaseVariable::Auto(name) => HashMap::from([(name.clone(), ty.clone())]),
			BaseVariable::Name(_) => HashMap::new(),
		},
		Tuple(fields) => fields.iter().map(|(_, field)| compute_upvars(field)).flatten().collect(),
		Projection { tuple, .. } => compute_upvars(tuple.as_ref()),
		Function {
			fixpoint_name,
			parameter,
			body,
			..
		} => {
			let mut body_upvars = compute_upvars(body);
			body_upvars.remove(parameter);
			if let Some(fixpoint_name) = fixpoint_name {
				body_upvars.remove(fixpoint_name);
			}
			body_upvars
		},
		Application { function, argument, .. } => {
			[&**function, &**argument].into_iter().map(compute_upvars).flatten().collect()
		},
		IntrinsicInvocation { intrinsic: _, arguments } => arguments.iter().map(compute_upvars).flatten().collect(),
		Assignment {
			assignee,
			definition,
			rest,
			..
		} => {
			let mut rest_upvars = compute_upvars(rest);
			rest_upvars.remove(assignee);
			rest_upvars.extend(compute_upvars(definition));
			rest_upvars
		},
		EqualityQuery { ty: _, left, right } => [&**left, &**right].into_iter().map(compute_upvars).flatten().collect(),
		CaseSplit { scrutinee, cases, .. } => [&**scrutinee]
			.into_iter()
			.chain(cases.iter().map(|(_, term)| &**term))
			.map(compute_upvars)
			.flatten()
			.collect(),
		Loop {
			parameter,
			argument,
			body,
			..
		} => {
			let mut body_upvars = compute_upvars(&*body);
			body_upvars.remove(parameter);
			body_upvars.extend(compute_upvars(argument));
			body_upvars
		},
		Step { argument, .. } => compute_upvars(&argument),
		Emit { argument, .. } => compute_upvars(&argument),
	}
}

struct Substitution(HashMap<Label, JuneTerm>);

fn substitute(term: &mut JuneTerm, substitution: &Substitution) {
	use JuneTerm::*;
	match term {
		Primitive(_) => (),
		Name(_, variable) => match variable {
			BaseVariable::Auto(name) => {
				if let Some(new_term) = substitution.0.get(name) {
					*term = new_term.clone();
				} else {
					()
				}
			},
			BaseVariable::Name(_) => (),
		},
		Tuple(fields) => {
			for (_, field) in fields {
				substitute(field, substitution)
			}
		},
		Closure { fields, .. } => {
			for field in fields {
				substitute(field, substitution)
			}
		},
		Projection { ty: _, tuple, index: _ } => substitute(tuple, substitution),
		Free { ty: _, share, index: _ } => substitute(share, substitution),
		Application { function, argument, .. } => {
			substitute(function, substitution);
			substitute(argument, substitution);
		},
		IntrinsicInvocation { arguments, .. } => {
			for argument in arguments {
				substitute(argument, substitution)
			}
		},
		Assignment { definition, rest, .. } => {
			// NOTE: Because every binding is fresh, shadowing doesn't concern us.
			substitute(definition, substitution);
			substitute(rest, substitution);
		},
		EqualityQuery { left, right, .. } => {
			substitute(left, substitution);
			substitute(right, substitution);
		},
		CaseSplit { ty, scrutinee, cases } => {
			substitute(scrutinee, substitution);
			for (_, case) in cases {
				substitute(case, substitution);
			}
		},
		Loop { argument, body, .. } => {
			// NOTE: Because every binding is fresh, shadowing doesn't concern us.
			substitute(argument, substitution);
			substitute(body, substitution);
		},
		Step { argument, .. } => substitute(argument, substitution),
		Emit { argument, .. } => substitute(argument, substitution),
	}
}

use std::collections::{HashSet};
use halfbrown::HashMap;

use super::symbol::SymbolGenerator;
use crate::interpreter::{
	cypress::{CypressBindingLabel, CypressOperation, CypressPrimitive, CypressTerm, CypressVariable},
	firefly::{
		FireflyBindingLabel, FireflyContinuationLabel, FireflyOperation, FireflyPrimitive, FireflyProcedure,
		FireflyProcedureLabel, FireflyProgram, FireflyStatement, FireflyTerm, FireflyTerminator, FireflyVariable,
	},
};

fn substitute_in_variable(
	variable: CypressVariable,
	substitution: &HashMap<CypressBindingLabel, CypressBindingLabel>,
) -> CypressVariable {
	match variable {
		CypressVariable::Local(local) => CypressVariable::Local(substitution.get(&local).cloned().unwrap_or(local)),
		other => other,
	}
}

pub fn substitute_in_operation(
	operation: CypressOperation,
	substitution: &HashMap<CypressBindingLabel, CypressBindingLabel>,
) -> CypressOperation {
	match operation {
		CypressOperation::EqualsQuery(xs) => CypressOperation::EqualsQuery(xs.map(|x| substitute_in_variable(x, substitution))),
		CypressOperation::Projection(tuple, index) => {
			CypressOperation::Projection(substitute_in_variable(tuple, substitution), index)
		},
		CypressOperation::Add(xs) => CypressOperation::Add(xs.map(|x| substitute_in_variable(x, substitution))),
		CypressOperation::Pair(xs) => CypressOperation::Pair(
			xs.into_vec()
				.into_iter()
				.map(|x| substitute_in_variable(x, substitution))
				.collect::<Vec<_>>()
				.into_boxed_slice(),
		),
	}
}

pub fn substitute(term: CypressTerm, mut substitution: HashMap<CypressBindingLabel, CypressBindingLabel>) -> CypressTerm {
	match term {
		CypressTerm::AssignValue {
			binding,
			ty,
			value,
			rest,
		} => {
			substitution.remove(&binding);
			CypressTerm::AssignValue {
				binding,
				ty,
				value,
				rest: Box::new(substitute(*rest, substitution)),
			}
		},
		CypressTerm::AssignOperation {
			binding,
			operation,
			rest,
		} => {
			substitution.remove(&binding);
			CypressTerm::AssignOperation {
				binding,
				operation: substitute_in_operation(operation, &substitution),
				rest: Box::new(substitute(*rest, substitution)),
			}
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
			let mut body_substitution = substitution.clone();
			if let Some(fixpoint_name) = fixpoint_name {
				body_substitution.remove(&fixpoint_name);
			}
			body_substitution.remove(&parameter);
			let body = substitute(*body, body_substitution);

			let mut rest_substitution = substitution;
			rest_substitution.remove(&binding);
			let rest = substitute(*rest, rest_substitution);

			CypressTerm::DeclareFunction {
				binding,
				fixpoint_name,
				domain,
				codomain,
				parameter,
				body: Box::new(body),
				rest: Box::new(rest),
			}
		},
		CypressTerm::DeclareContinuation {
			label,
			domain,
			parameter,
			body,
			rest,
		} => {
			let mut body_substitution = substitution.clone();
			body_substitution.remove(&parameter);
			let body = substitute(*body, body_substitution);

			let rest_substitution = substitution;
			let rest = substitute(*rest, rest_substitution);

			CypressTerm::DeclareContinuation {
				label,
				domain,
				parameter,
				body: Box::new(body),
				rest: Box::new(rest),
			}
		},
		CypressTerm::CaseSplit {
			scrutinee,
			yes_continuation,
			no_continuation,
		} => CypressTerm::CaseSplit {
			scrutinee: substitute_in_variable(scrutinee, &substitution),
			yes_continuation,
			no_continuation,
		},
		CypressTerm::Apply {
			function,
			continuation,
			argument,
		} => CypressTerm::Apply {
			function: substitute_in_variable(function, &substitution),
			continuation,
			argument: substitute_in_variable(argument, &substitution),
		},
		CypressTerm::Continue {
			continuation_label,
			argument,
		} => CypressTerm::Continue {
			continuation_label,
			argument: substitute_in_variable(argument, &substitution),
		},
		CypressTerm::Halt { argument } => CypressTerm::Halt {
			argument: substitute_in_variable(argument, &substitution),
		},
	}
}

fn get_if_local(variable: &CypressVariable) -> Option<CypressBindingLabel> {
	if let CypressVariable::Local(label) = variable {
		Some(label.clone())
	} else {
		None
	}
}

pub fn compute_free_variables_in_operation(operation: &CypressOperation) -> HashSet<CypressBindingLabel> {
	match operation {
		CypressOperation::EqualsQuery(x) => x.into_iter().filter_map(get_if_local).collect(),
		CypressOperation::Projection(tuple, _) => [tuple].into_iter().filter_map(get_if_local).collect(),
		CypressOperation::Add(x) => x.into_iter().filter_map(get_if_local).collect(),
		CypressOperation::Pair(vs) => (*vs).into_iter().filter_map(get_if_local).collect(),
	}
}

pub fn compute_free_variables_in_term(term: &CypressTerm) -> HashSet<CypressBindingLabel> {
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
		} => [scrutinee].into_iter().filter_map(get_if_local).collect(),
		CypressTerm::Apply {
			function,
			continuation: _,
			argument,
		} => [function, argument].into_iter().filter_map(get_if_local).collect(),
		CypressTerm::Continue {
			continuation_label: _,
			argument,
		} => [argument].into_iter().filter_map(get_if_local).collect(),
		CypressTerm::Halt { argument } => [argument].into_iter().filter_map(get_if_local).collect(),
	}
}

pub fn hoist_variable(variable: CypressVariable) -> FireflyVariable {
	match variable {
		CypressVariable::Local(x) => FireflyVariable::Local(x),
		CypressVariable::Name(y) => FireflyVariable::Global(y),
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
		CypressOperation::EqualsQuery(x) => FireflyOperation::EqualsQuery(x.map(hoist_variable)),
		CypressOperation::Projection(tuple, index) => FireflyOperation::Projection(hoist_variable(tuple), index),
		CypressOperation::Add(x) => FireflyOperation::Add(x.map(hoist_variable)),
		CypressOperation::Pair(x) => FireflyOperation::Pair(
			x.into_vec()
				.into_iter()
				.map(hoist_variable)
				.collect::<Vec<_>>()
				.into_boxed_slice(),
		),
	}
}

pub fn hoist_term(
	term: CypressTerm,
	procedures: &mut HashMap<FireflyProcedureLabel, FireflyProcedure>,
	symbol_generator: &mut SymbolGenerator,
) -> FireflyTerm {
	match term {
		CypressTerm::AssignValue {
			binding,
			ty: _,
			value,
			rest,
		} => {
			let mut rest = hoist_term(*rest, procedures, symbol_generator);
			rest.statements.push(FireflyStatement::AssignPrimitive {
				binding: FireflyBindingLabel(binding),
				value: hoist_primitive(value),
			});
			rest
		},
		CypressTerm::AssignOperation {
			binding,
			operation,
			rest,
		} => {
			let mut rest = hoist_term(*rest, procedures, symbol_generator);
			rest.statements.push(FireflyStatement::AssignOperation {
				binding: FireflyBindingLabel(binding),
				operation: hoist_operation(operation),
			});
			rest
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
			let mut body_free_variables = compute_free_variables_in_term(&body);
			body_free_variables.remove(&parameter);
			fixpoint_name.map(|fixpoint_name| body_free_variables.remove(&fixpoint_name));

			let environment_arguments_to_parameters = body_free_variables
				.iter()
				.cloned()
				.map(|environment_argument| {
					let environment_parameter = symbol_generator.fresh();
					(environment_argument, environment_parameter)
				})
				.collect::<HashMap<_, _>>();

			let body = substitute(*body, environment_arguments_to_parameters.clone());
			let mut body = hoist_term(body, procedures, symbol_generator);

			let environment_parameters_to_arguments = environment_arguments_to_parameters
				.into_iter()
				.map(|(environment_argument, environment_parameter)| {
					(
						FireflyBindingLabel(environment_parameter),
						FireflyBindingLabel(environment_argument),
					)
				})
				.collect::<HashMap<_, _>>();

			let environment_parameters = environment_parameters_to_arguments
				.iter()
				.map(|(environment_parameter, _)| environment_parameter)
				.cloned()
				.collect::<HashSet<_>>();

			let procedure_label = symbol_generator.fresh();

			if let Some(fixpoint_name) = fixpoint_name {
				body.statements.push(FireflyStatement::AssignClosure {
					binding: FireflyBindingLabel(fixpoint_name),
					procedure: FireflyProcedureLabel(procedure_label),
					environment_parameters_to_arguments: environment_parameters
						.iter()
						.cloned()
						.map(|parameter| (parameter, parameter))
						.collect::<HashMap<_, _>>(),
				});
			}

			// TODO: Surround hoisted body term with let bindings that unpack the locals from the environment. (or do we want to do this at a later stage, such as when translating to Sierra?)

			let procedure = FireflyProcedure {
				fixpoint_variable: fixpoint_name.map(FireflyBindingLabel),
				environment_parameters,
				parameter: FireflyBindingLabel(parameter),
				body,
			};

			procedures.insert(FireflyProcedureLabel(procedure_label), procedure);

			let mut rest = hoist_term(*rest, procedures, symbol_generator);

			rest.statements.push(FireflyStatement::AssignClosure {
				binding: FireflyBindingLabel(binding),
				procedure: FireflyProcedureLabel(procedure_label),
				environment_parameters_to_arguments,
			});

			rest
		},
		CypressTerm::DeclareContinuation {
			label,
			domain: _,
			parameter,
			body,
			rest,
		} => {
			let mut rest = hoist_term(*rest, procedures, symbol_generator);
			rest.statements.push(FireflyStatement::DeclareContinuation {
				label: FireflyContinuationLabel(label),
				parameter: FireflyBindingLabel(parameter),
				body: hoist_term(*body, procedures, symbol_generator),
			});
			rest
		},
		CypressTerm::CaseSplit {
			scrutinee,
			yes_continuation,
			no_continuation,
		} => FireflyTerm::new(FireflyTerminator::Branch {
			scrutinee: hoist_variable(scrutinee),
			yes_continuation: FireflyContinuationLabel(yes_continuation),
			no_continuation: FireflyContinuationLabel(no_continuation),
		}),
		CypressTerm::Apply {
			function,
			continuation,
			argument,
		} => FireflyTerm::new(FireflyTerminator::Apply {
			closure: hoist_variable(function),
			continuation_label: continuation.map(FireflyContinuationLabel),
			argument: hoist_variable(argument),
		}),
		CypressTerm::Continue {
			continuation_label,
			argument,
		} => FireflyTerm::new(FireflyTerminator::Jump {
			continuation_label: continuation_label.map(FireflyContinuationLabel),
			argument: hoist_variable(argument),
		}),
		CypressTerm::Halt { argument } => FireflyTerm::new(FireflyTerminator::Halt {
			argument: hoist_variable(argument),
		}),
	}
}

// Closure conversion turns functions, which may have free variables, into closures, which bundle a procedure label and an environment.
// All nested function declarations are hoisted to the top level of the program as first-order procedures.
pub fn hoist_program(term: CypressTerm, symbol_generator: &mut SymbolGenerator) -> FireflyProgram {
	let mut procedures = HashMap::<FireflyProcedureLabel, FireflyProcedure>::new();

	let entry = hoist_term(term, &mut procedures, symbol_generator);

	FireflyProgram {
		procedures,
		entry,
		symbol_generator: symbol_generator.clone(),
	}
}

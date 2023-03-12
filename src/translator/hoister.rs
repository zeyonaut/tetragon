use std::collections::{HashMap, HashSet};

use super::symbol::SymbolGenerator;
use crate::interpreter::{
	cypress::{CypressBindingLabel, CypressOperation, CypressPrimitive, CypressTerm, CypressVariable},
	firefly::{
		FireflyBindingLabel, FireflyContinuationLabel, FireflyOperation, FireflyPrimitive, FireflyProcedure,
		FireflyProcedureLabel, FireflyProgram, FireflyTerm, FireflyVariable,
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

/*
I'm thinking: in an outer lambda, the environment variables are rebound via let bindings to fresh variables (which are then substituted in the body).
But in a nested lambda, this nested one gains the environment of the outer as a special environment parameter...
No, scratch that idea, let's make environments flat. If we're rebinding the environment variables anyway, we might as well use them as the next free variables for any more nested functions.
*/

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
		} => FireflyTerm::AssignPrimitive {
			binding: FireflyBindingLabel(binding),
			value: hoist_primitive(value),
			rest: Box::new(hoist_term(*rest, procedures, symbol_generator)),
		},
		CypressTerm::AssignOperation {
			binding,
			operation,
			rest,
		} => FireflyTerm::AssignOperation {
			binding: FireflyBindingLabel(binding),
			operation: hoist_operation(operation),
			rest: Box::new(hoist_term(*rest, procedures, symbol_generator)),
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
			let body_free_variables = compute_free_variables_in_term(&body);

			let arguments_to_parameters = body_free_variables
				.iter()
				.cloned()
				.map(|argument| {
					let parameter = symbol_generator.fresh();
					(argument, parameter)
				})
				.collect::<HashMap<_, _>>();

			let body = substitute(*body, arguments_to_parameters.clone());
			let body = hoist_term(body, procedures, symbol_generator);

			let parameters_to_arguments = arguments_to_parameters
				.into_iter()
				.map(|(argument, parameter)| (FireflyBindingLabel(parameter), FireflyBindingLabel(argument)))
				.collect::<HashMap<_, _>>();

			let procedure = FireflyProcedure {
				fixpoint_variable: fixpoint_name.map(FireflyBindingLabel),
				environment_parameters: body_free_variables.into_iter().map(FireflyBindingLabel).collect(),
				parameter: FireflyBindingLabel(parameter),
				body,
			};

			let procedure_label = symbol_generator.fresh();

			procedures.insert(FireflyProcedureLabel(procedure_label), procedure);

			FireflyTerm::AssignClosure {
				binding: FireflyBindingLabel(binding),
				procedure: FireflyProcedureLabel(procedure_label),
				environment_parameters_to_arguments: parameters_to_arguments,
				rest: Box::new(hoist_term(*rest, procedures, symbol_generator)),
			}
		},
		CypressTerm::DeclareContinuation {
			label,
			domain: _,
			parameter,
			body,
			rest,
		} => FireflyTerm::DeclareContinuation {
			label: FireflyContinuationLabel(label),
			parameter: FireflyBindingLabel(parameter),
			body: Box::new(hoist_term(*body, procedures, symbol_generator)),
			rest: Box::new(hoist_term(*rest, procedures, symbol_generator)),
		},
		CypressTerm::CaseSplit {
			scrutinee,
			yes_continuation,
			no_continuation,
		} => FireflyTerm::Branch {
			scrutinee: hoist_variable(scrutinee),
			yes_continuation: FireflyContinuationLabel(yes_continuation),
			no_continuation: FireflyContinuationLabel(no_continuation),
		},
		CypressTerm::Apply {
			function,
			continuation,
			argument,
		} => FireflyTerm::Apply {
			closure: hoist_variable(function),
			continuation_label: continuation.map(FireflyContinuationLabel),
			argument: hoist_variable(argument),
		},
		CypressTerm::Continue {
			continuation_label,
			argument,
		} => FireflyTerm::Jump {
			continuation_label: continuation_label.map(FireflyContinuationLabel),
			argument: hoist_variable(argument),
		},
		CypressTerm::Halt { argument } => FireflyTerm::Halt {
			argument: hoist_variable(argument),
		},
	}
}

// Closure conversion turns functions, which may have free variables, into closures, which bundle a procedure label and an environment.
// All nested function declarations are hoisted to the top level of the program as first-order procedures.
pub fn hoist_program(term: CypressTerm, symbol_generator: &mut SymbolGenerator) -> FireflyProgram {
	let mut procedures = HashMap::<FireflyProcedureLabel, FireflyProcedure>::new();

	let entry = hoist_term(term, &mut procedures, symbol_generator);

	FireflyProgram { procedures, entry }
}

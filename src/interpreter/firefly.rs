use std::{collections::{HashMap, HashSet}, hash::Hash};

use crate::utility::slice::Slice;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum FireflyVariable {
	Local(u64),
	Global(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FireflyProcedureLabel(pub u64);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FireflyContinuationLabel(pub u64);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FireflyBindingLabel(pub u64);


#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FireflyType {
	Unity,
	Polarity,
	Integer,
	Power { domain: Box<Self>, codomain: Box<Self> },
	Product(Vec<Self>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyValue {
	Unity,
	Polarity(bool),
	Integer(i64),
	Tuple(Vec<Self>),
	Closure(FireflyProcedureLabel, Vec<Self>),
	Extern(String),
}

// Primitives are essentially nullary operations that can't fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyPrimitive {
	Unity,
	Polarity(bool),
	Integer(i64),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyOperation {
	Free(FireflyBindingLabel),
	EqualsQuery([FireflyVariable; 2]),
	Projection(FireflyVariable, usize),
	Add([FireflyVariable; 2]),
	Pair(Slice<FireflyVariable>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FireflyTerm {
	AssignPrimitive {
		binding: FireflyBindingLabel,
		value: FireflyPrimitive,
		rest: Box<Self>,
	},
	AssignOperation {
		binding: FireflyBindingLabel,
		operation: FireflyOperation,
		rest: Box<Self>,
	},
	AssignClosure {
		binding: FireflyBindingLabel,
		procedure: FireflyProcedureLabel,
		environment_parameters_to_arguments: HashMap<FireflyBindingLabel, FireflyBindingLabel>,
		rest: Box<Self>,
	},
	DeclareContinuation {
		label: FireflyContinuationLabel,
		parameter: FireflyBindingLabel,
		body: Box<Self>,
		rest: Box<Self>,
	},
	Branch {
		scrutinee: FireflyVariable,
		yes_continuation: FireflyContinuationLabel,
		no_continuation: FireflyContinuationLabel,
	},
	Apply {
		closure: FireflyVariable,
		continuation_label: Option<FireflyContinuationLabel>,
		argument: FireflyVariable,
	},
	Jump {
		continuation_label: Option<FireflyContinuationLabel>,
		argument: FireflyVariable,
	},
	Halt {
		argument: FireflyVariable,
	},
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FireflyProcedure {
	pub fixpoint_variable: Option<FireflyBindingLabel>,
	pub environment_parameters: HashSet<FireflyBindingLabel>,
	pub parameter: FireflyBindingLabel,
	pub body: FireflyTerm,
}

#[derive(Debug)]
pub struct FireflyProgram {
	pub procedures: HashMap<FireflyProcedureLabel, FireflyProcedure>,
	pub entry: FireflyTerm,
}
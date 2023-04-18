use std::hash::Hash;

use crate::{translator::label::Label, utility::slice::Slice};

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum CypressVariable {
	Local(Label),
	Global(String),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum CypressProjector {
	Field(usize),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct CypressProjection {
	pub root: CypressVariable,
	pub projectors: Vec<CypressProjector>,
}

impl CypressProjection {
	pub fn new(root: CypressVariable) -> Self {
		Self {
			root,
			projectors: Vec::new(),
		}
	}

	pub fn project(mut self, projector: CypressProjector) -> Self {
		self.projectors.push(projector);
		self
	}
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CypressType {
	Unity,
	Polarity,
	Integer,
	Power { domain: Box<Self>, codomain: Box<Self> },
	Product(Slice<Self>),
}

// Primitives are essentially nullary operations that can't fail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CypressPrimitive {
	Unity,
	Polarity(bool),
	Integer(i64),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CypressOperation {
	Id(CypressType, CypressProjection),
	EqualsQuery(CypressType, [CypressProjection; 2]),
	Add([CypressProjection; 2]),
	Pair(Slice<(CypressType, CypressProjection)>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CypressStatement {
	AssignValue {
		binding: Label,
		ty: CypressType,
		value: CypressPrimitive,
	},
	AssignOperation {
		binding: Label,
		operation: CypressOperation,
	},
	DeclareFunction {
		binding: Label,
		fixpoint_name: Option<Label>,
		domain: CypressType,
		codomain: CypressType,
		parameter: Label,
		body: Box<CypressTerm>,
	},
	DeclareContinuation {
		label: Label,
		domain: CypressType,
		parameter: Label,
		body: Box<CypressTerm>,
	},
}

impl CypressStatement {
	pub fn prepend_to(self, mut term: CypressTerm) -> CypressTerm {
		term.statements.insert(0, self);
		term
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CypressTerminator {
	Branch {
		scrutinee: CypressProjection,
		yes_continuation: Label,
		no_continuation: Label,
	}, // Continuations should have unit domain. (For now.) Scrutinee should be a polarity.
	Apply {
		function: CypressProjection,
		domain: CypressType,
		codomain: CypressType,
		continuation: Option<Label>,
		argument: CypressProjection,
	},
	Jump {
		continuation_label: Option<Label>,
		argument: CypressProjection,
		domain: CypressType,
	},
}

impl From<CypressTerminator> for CypressTerm {
	fn from(value: CypressTerminator) -> Self {
		Self::new(vec![], value)
	}
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CypressTerm {
	pub statements: Vec<CypressStatement>,
	pub terminator: CypressTerminator,
}

impl CypressTerm {
	pub fn new(statements: Vec<CypressStatement>, terminator: CypressTerminator) -> Self {
		Self { statements, terminator }
	}

	pub fn compose(mut statements: Vec<CypressStatement>, mut term: Self) -> Self {
		Self {
			statements: {
				statements.append(&mut term.statements);
				statements
			},
			terminator: term.terminator,
		}
	}
}

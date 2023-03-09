#[derive(Clone)]
pub enum CypressVariable {
	Auto(u64),
	Name(String),
}

#[derive(Copy, Clone)]
pub struct CypressLabel(pub u64);

#[derive(Clone)]
pub enum CypressType {
	Unity,
	Polarity,
	Integer,
	Power { domain: Box<Self>, codomain: Box<Self> },
}

pub enum CypressValue {
	Unity,
	Polarity(bool),
	Integer(i64),
}

pub enum CypressOperation {
	EqualsQuery([CypressVariable; 2]),
}

pub enum CypressTerm {
	AssignValue {
		binding: CypressVariable,
		ty: CypressType,
		value: CypressValue,
		rest: Box<Self>,
	},
	AssignOperation {
		binding: CypressVariable,
		ty: CypressType,
		operation: CypressOperation,
		rest: Box<Self>,
	},
	DeclareFunction {
		fixpoint_name: Option<String>,
		binding: CypressVariable,
		domain: CypressType,
		codomain: CypressType,
		continuation: CypressLabel,
		parameter: CypressVariable,
		body: Box<Self>,
		rest: Box<Self>,
	},
	DeclareContinuation {
		label: CypressLabel,
		domain: CypressType,
		argument: CypressVariable,
		body: Box<Self>,
		rest: Box<Self>,
	},
	CaseSplit {
		scrutinee: CypressVariable,
		yes_continuation: CypressLabel,
		no_continuation: CypressLabel,
	}, // Continuations should have unit domain. (For now.) Scrutinee should be a polarity.
	Apply {
		function: CypressVariable,
		continuation: CypressLabel,
		argument: CypressVariable,
	},
	Continue {
		continuation: CypressLabel,
		argument: CypressVariable,
	},
	Halt {
		argument: CypressVariable,
	},
}

impl CypressTerm {
	pub fn interpret(self) -> CypressValue {
		todo!()
	}
}

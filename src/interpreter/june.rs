use std::collections::HashMap;

use super::base::BaseVariable;
use crate::translator::label::{Label, LabelGenerator};

#[derive(Debug)]
pub struct JuneProgram {
	pub procedures: HashMap<Label, JuneProcedure>,
	pub entry: Label,
	pub symbol_generator: LabelGenerator,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JuneProcedure {
	pub domain: JuneType,
	pub parameter: Option<Label>,
	pub capture: Option<(Label, Vec<JuneType>)>,
	pub body: JuneTerm,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JuneType {
	Empty,
	Unity,
	Polarity,
	Integer,
	Product(Vec<Self>),
	Procedure { domain: Box<Self>, codomain: Box<Self> },
	Share(Option<Vec<Self>>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JuneIntrinsic {
	Add,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JuneTerm {
	Polarity(bool),
	Integer(i64),
	Name(JuneType, BaseVariable),
	Tuple(Vec<(JuneType, Self)>),
	Procedure {
		domain: JuneType,
		codomain: JuneType,
		procedure: Label,
	},
	Projection {
		ty: JuneType,
		tuple: Box<Self>,
		index: usize,
	},
	Free {
		ty: JuneType,
		share: Box<Self>,
		index: usize,
	},
	Closure {
		domain: JuneType,
		codomain: JuneType,
		procedure: Label,
		fields: Vec<Self>,
	},
	Application {
		codomain: JuneType,
		function: Box<Self>,
		argument: Box<Self>,
	},
	IntrinsicInvocation {
		intrinsic: JuneIntrinsic,
		arguments: Vec<Self>,
	},
	Assignment {
		ty: JuneType,
		assignee: Label,
		definition: Box<Self>,
		rest: Box<Self>,
	},
	EqualityQuery {
		ty: JuneType,
		left: Box<Self>,
		right: Box<Self>,
	},
	CaseSplit {
		ty: JuneType,
		scrutinee: Box<Self>,
		cases: Vec<(bool, Box<Self>)>,
	},
	Loop {
		codomain: JuneType,
		loop_name: Label,
		parameter: Label,
		argument: Box<Self>,
		body: Box<Self>,
	},
	Step {
		loop_name: Label,
		argument: Box<Self>,
	},
	Emit {
		loop_name: Label,
		argument: Box<Self>,
	},
}

impl JuneTerm {
	pub fn ty(&self) -> JuneType {
		use JuneType::*;
		match self {
			Self::Polarity(_) => Polarity,
			Self::Integer(_) => Integer,
			Self::Procedure { domain, codomain, .. } => Procedure {
				domain: Box::new(domain.clone()),
				codomain: Box::new(codomain.clone()),
			},
			Self::Name(ty, _) => ty.clone(),
			Self::Tuple(typed_terms) => Product(typed_terms.iter().map(|(ty, _)| ty).cloned().collect()),
			Self::Projection { ty, .. } => ty.clone(),
			Self::Free { ty, .. } => ty.clone(),
			Self::Closure {
				domain,
				codomain,
				fields,
				..
			} => Product(vec![
				Procedure {
					domain: Box::new(domain.clone()),
					codomain: Box::new(codomain.clone()),
				},
				Share(Some(fields.iter().map(|field| field.ty()).collect())),
			]),
			Self::Application { codomain: ty, .. } => ty.clone(),
			Self::IntrinsicInvocation {
				intrinsic: JuneIntrinsic::Add,
				..
			} => Integer,
			Self::Assignment { ty, .. } => ty.clone(),
			Self::EqualityQuery { .. } => Polarity,
			Self::CaseSplit {
				ty,
				scrutinee: _,
				cases: _,
			} => ty.clone(),
			Self::Loop { codomain, .. } => codomain.clone(),
			Self::Step { .. } => Empty,
			Self::Emit { .. } => Empty,
		}
	}
}

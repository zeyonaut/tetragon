use enum_iterator::Sequence;

use super::lexer::{LexError, Lexer, Terminal, Token};
use crate::{
	generator::{
		grammar::{grammar, Symbol},
		lalr1::{self, GenerateParserError, ParseError},
	},
	util::{
		pow::impl_downset_for_repr_enum,
		slice::{match_slice, Slice},
	},
};

#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
#[repr(u8)]
enum Nonterminal {
	Value,
	DelimitedValue,
	AppliedValue,
	Type,
	DelimitedType,
	Cases,
}

impl_downset_for_repr_enum![Nonterminal ~ u8];

#[derive(Debug)]
pub enum Type {
	Name(String),
	Power { domain: Box<Self>, codomain: Box<Self> },
}

#[derive(Debug)]
pub enum Value {
	Integer(i64),
	Name(String),
	Function {
		binding: String,
		ty: Type,
		body: Box<Self>,
	},
	Fixpoint {
		binding: String,
		body: Box<Self>,
	},
	Application {
		function: Box<Self>,
		argument: Box<Self>,
	},
	Assignment {
		binding: String,
		definition: Box<Self>,
		rest: Box<Self>,
	},
	EqualityQuery {
		left: Box<Self>,
		right: Box<Self>,
	},
	CaseSplit {
		scrutinee: Box<Self>,
		cases: Cases,
	},
}

#[derive(Debug)]
pub struct Cases {
	cases: Vec<(String, Box<Value>)>,
}

#[derive(Debug)]
pub enum Node {
	Value(Value),
	Type(Type),
	Cases(Cases),
	Fail,
}

// TODO: Allow fallible node production (with early return).
// TODO: We can't pattern match on owned slices (not even with box_patterns!) and gain ownership of their contents, so this is the best we can do, unfortunately.
// NOTE: This should follow the structure of the grammar written as written in (*).
fn produce_node(target: Nonterminal, pattern: Slice<Symbol<Node, Token>>) -> Node {
	use Symbol::{Nonterminal as Nx, Terminal as Tx};
	use Token::*;
	match target {
		Nonterminal::Value => {
			match_slice! { pattern;
				[Nx(Node::Value(value))] => {
					Node::Value(value)
				},
				[Tx(Name(binding)), Tx(Bicolon), Nx(Node::Value(definition)), Nx(Node::Value(rest))] => {
					Node::Value(Value::Assignment {
						binding,
						definition: Box::new(definition),
						rest: Box::new(rest),
					})
				},
				[Nx(Node::Value(left)), Tx(EqualsQuestion), Nx(Node::Value(right))] => {
					Node::Value(Value::EqualityQuery {
						left: Box::new(left),
						right: Box::new(right),
					})
				},
				[Nx(Node::Value(scrutinee)), Tx(Question), Nx(Node::Cases(cases))] => {
					Node::Value(Value::CaseSplit {
						scrutinee: Box::new(scrutinee),
						cases,
					})
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::AppliedValue => {
			match_slice! { pattern;
				[Nx(Node::Value(value))] => {
					Node::Value(value)
				},
				[Nx(Node::Value(function)), Nx(Node::Value(argument))] => {
					Node::Value(Value::Application {
						function: Box::new(function),
						argument: Box::new(argument)
					})
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::DelimitedValue => {
			match_slice! { pattern;
				[Tx(IntegerLiteral(integer))] => {
					Node::Value(Value::Integer(integer))
				},
				[Tx(Name(name))] => {
					Node::Value(Value::Name(name))
				},
				[Tx(OpenOrtho), Nx(Node::Value(value)), Tx(CloseOrtho)] => {
					Node::Value(value)
				},
				[Tx(OpenCurly), Tx(Name(binding)), Nx(Node::Type(ty)), Tx(CloseCurly), Nx(Node::Value(body))] => {
					Node::Value(Value::Function { binding, ty, body: Box::new(body) })
				},
				[Tx(OpenCurly), Tx(Name(binding)), Tx(Arrova), Tx(CloseCurly), Nx(Node::Value(body))] => {
					Node::Value(Value::Fixpoint { binding, body: Box::new(body) })
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::Cases => {
			match_slice! { pattern;
				[] => {
					Node::Cases(Cases { cases: Vec::new() })
				},
				[Nx(Node::Cases(Cases {cases})), Tx(Name(name)), Tx(Bar), Nx(Node::Value(value))] => {
					Node::Cases({ let mut cases = cases; cases.push((name, Box::new(value))); Cases { cases }})
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::Type => {
			match_slice! { pattern;
				[Nx(Node::Type(ty))] => {
					Node::Type(ty)
				},
				[Nx(Node::Type(domain)), Tx(Arrow), Nx(Node::Type(codomain))] => {
					Node::Type(Type::Power {
						domain: Box::new(domain),
						codomain: Box::new(codomain),
					})
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::DelimitedType => {
			match_slice! { pattern;
				[Tx(Name(name))] => {
					Node::Type(Type::Name(name))
				},
				_ => Node::Fail,
			}
		},
	}
}

pub struct Parser {
	parser: lalr1::Parser<Nonterminal, Terminal>,
}

impl Parser {
	pub fn new() -> Result<Self, GenerateParserError> {
		use Nonterminal::*;
		use Terminal::*;
		// NOTE: (*) (Don't remove this comment)
		let grammar = grammar![
			Value;
			Value => [
				[@AppliedValue],
				[!Name, !Bicolon, @DelimitedValue, @Value],      // Assignment
				[@AppliedValue, !EqualsQuestion, @AppliedValue], // Equality query
				[@DelimitedValue, !Question, @Cases]             // Case split
			]
			AppliedValue => [
				[@DelimitedValue],
				[@AppliedValue, @DelimitedValue], // Function Application
			]
			DelimitedValue => [
				[!IntegerLiteral],
				[!Name],
				[!OpenOrtho, @Value, !CloseOrtho],
				[!OpenCurly, !Name, @Type, !CloseCurly, @DelimitedValue],   // Lambda binding
				[!OpenCurly, !Name, !Arrova, !CloseCurly, @DelimitedValue], // Mu binding
			]
			Cases => [
				[],                                     // Empty cases
				[@Cases, !Name, !Bar, @DelimitedValue], // Inhabited cases
			]
			Type => [
				[@DelimitedType],
				[@DelimitedType, !Arrow, @Type], // Function type
			]
			DelimitedType => [
				[!Name],
			]
		];
		Ok(Self {
			parser: lalr1::Parser::new(&grammar)?,
		})
	}

	pub fn parse(&self, lexer: Lexer) -> Result<Node, ParseError<LexError>> {
		self.parser.parse(lexer, produce_node)
	}
}

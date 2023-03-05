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

#[derive(Clone, Debug)]
pub enum ParsedType {
	Name(String),
	Power { domain: Box<Self>, codomain: Box<Self> },
	Polarity,
	Integer,
}

#[derive(Clone, Debug)]
pub enum ParsedTerm {
	Polarity(bool),
	Integer(i64),
	Name(String),
	Function {
		binding: String,
		domain: ParsedType,
		codomain: ParsedType,
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
		cases: ParsedCases,
	},
}

#[derive(Clone, Debug)]
pub struct ParsedCases {
	pub cases: Vec<(bool, Box<ParsedTerm>)>,
}

#[derive(Debug)]
pub enum Node {
	Term(ParsedTerm),
	Type(ParsedType),
	Cases(ParsedCases),
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
				[Nx(Node::Term(term))] => {
					Node::Term(term)
				},
				[Tx(Name(binding)), Tx(Bicolon), Nx(Node::Term(definition)), Nx(Node::Term(rest))] => {
					Node::Term(ParsedTerm::Assignment {
						binding,
						definition: Box::new(definition),
						rest: Box::new(rest),
					})
				},
				[Nx(Node::Term(left)), Tx(EqualsQuestion), Nx(Node::Term(right))] => {
					Node::Term(ParsedTerm::EqualityQuery {
						left: Box::new(left),
						right: Box::new(right),
					})
				},
				[Nx(Node::Term(scrutinee)), Tx(Question), Nx(Node::Cases(cases))] => {
					Node::Term(ParsedTerm::CaseSplit {
						scrutinee: Box::new(scrutinee),
						cases,
					})
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::AppliedValue => {
			match_slice! { pattern;
				[Nx(Node::Term(term))] => {
					Node::Term(term)
				},
				[Nx(Node::Term(function)), Nx(Node::Term(argument))] => {
					Node::Term(ParsedTerm::Application {
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
					Node::Term(ParsedTerm::Integer(integer))
				},
				[Tx(Name(name))] => {
					match name.as_ref() {
						"yes" => Node::Term(ParsedTerm::Polarity(true)),
						"no" => Node::Term(ParsedTerm::Polarity(false)),
						_ => Node::Term(ParsedTerm::Name(name)),
					}
				},
				[Tx(OpenOrtho), Nx(Node::Term(term)), Tx(CloseOrtho)] => {
					Node::Term(term)
				},
				[Tx(OpenCurly), Tx(Name(binding)), Nx(Node::Type(domain)), Tx(CloseCurly), Tx(Arrow), Nx(Node::Type(codomain)), Nx(Node::Term(body))] => {
					Node::Term(ParsedTerm::Function { binding, domain, codomain, body: Box::new(body) })
				},
				[Tx(OpenCurly), Tx(Name(binding)), Tx(Arrova), Tx(CloseCurly), Nx(Node::Term(body))] => {
					Node::Term(ParsedTerm::Fixpoint { binding, body: Box::new(body) })
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::Cases => {
			match_slice! { pattern;
				[] => {
					Node::Cases(ParsedCases { cases: Vec::new() })
				},
				[Nx(Node::Cases(ParsedCases {cases})), Nx(Node::Term(ParsedTerm::Polarity(polarity))), Tx(Bar), Nx(Node::Term(term))] => {
					Node::Cases({ let mut cases = cases; cases.push((polarity, Box::new(term))); ParsedCases { cases }})
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
					Node::Type(ParsedType::Power {
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
					match name.as_ref() {
						"Int" => Node::Type(ParsedType::Integer),
						"Pol" => Node::Type(ParsedType::Polarity),
						_ => Node::Type(ParsedType::Name(name)),
					}
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
				[!OpenCurly, !Name, @Type, !CloseCurly, !Arrow, @DelimitedType, @DelimitedValue],   // Lambda binding
				[!OpenCurly, !Name, !Arrova, !CloseCurly, @DelimitedValue], // Mu binding
			]
			Cases => [
				[],                                               // Empty cases
				[@Cases, @DelimitedValue, !Bar, @DelimitedValue], // Inhabited cases
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

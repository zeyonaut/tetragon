use enum_iterator::Sequence;

use super::lexer::{LexError, Lexer, Terminal, Token};
use crate::{
	generator::{
		grammar::{grammar, Symbol},
		lalr1::{self, GenerateParserError, ParseError},
	},
	utility::{
		pow::impl_downset_for_repr_enum,
		slice::{match_slice, Slice},
	},
};

#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
#[repr(u8)]
enum Nonterminal {
	Value,
	DelimitedValue,
	SmallValue,
	LongValue,
	AppliedValue,
	ValueList,
	IntrinsicInvocation,
	Type,
	DelimitedType,
	TypeList,
	Cases,
}

impl_downset_for_repr_enum![Nonterminal ~ u8];

#[derive(Clone, Debug)]
pub enum ParsedType {
	Name(String),
	Product(Vec<Self>),
	Power { domain: Box<Self>, codomain: Box<Self> },
	Polarity,
	Integer,
}

#[derive(Clone, Debug)]
pub enum ParsedTerm {
	Polarity(bool),
	Integer(i64),
	Name(String),
	Tuple(Vec<Self>),
	Projection {
		tuple: Box<Self>,
		index: usize,
	},
	Function {
		parameter: String,
		domain: ParsedType,
		codomain: Option<ParsedType>,
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
	IntrinsicInvocation {
		intrinsic: String,
		arguments: Vec<Self>,
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
	Loop {
		loop_name: String,
		argument: Box<Self>,
		parameter: String,
		codomain: ParsedType,
		body: Box<Self>,
	},
	Step {
		loop_name: String,
		argument: Box<Self>,
	},
	Emit {
		loop_name: String,
		argument: Box<Self>,
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
	ValueList(Vec<ParsedTerm>),
	TypeList(Vec<ParsedType>),
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
		Nonterminal::LongValue => {
			match_slice! { pattern;
				[Nx(Node::Term(term))] => {
					Node::Term(term)
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
				[Nx(Node::Term(term))] => {
					Node::Term(term)
				},
				[Tx(OpenCurly), Tx(Name(parameter)), Nx(Node::Type(domain)), Tx(CloseCurly), Tx(Arrow), Nx(Node::Type(codomain)), Nx(Node::Term(body))] => {
					Node::Term(ParsedTerm::Function { parameter, domain, codomain: Some(codomain), body: Box::new(body) })
				},
				[Tx(OpenCurly), Tx(Name(parameter)), Nx(Node::Type(domain)), Tx(CloseCurly), Nx(Node::Term(body))] => {
					Node::Term(ParsedTerm::Function { parameter, domain, codomain: None, body: Box::new(body) })
				},
				[Tx(OpenCurly), Tx(Name(binding)), Tx(Arrova), Tx(CloseCurly), Nx(Node::Term(body))] => {
					Node::Term(ParsedTerm::Fixpoint { binding, body: Box::new(body) })
				},
				[Tx(OpenCurly), Tx(Name(loop_name)), Tx(Ampersand), Tx(CloseCurly), Nx(Node::Term(argument)), Tx(OpenCurly), Tx(Name(parameter)), Tx(CloseCurly), Tx(Arrow), Nx(Node::Type(codomain)), Nx(Node::Term(body))] => {
					Node::Term(ParsedTerm::Loop { loop_name, argument: Box::new(argument), parameter, codomain, body: Box::new(body) })
				},
				[Tx(Name(loop_name)), Tx(Step), Nx(Node::Term(body))] => {
					Node::Term(ParsedTerm::Step { loop_name, argument: Box::new(body) })
				},
				[Tx(Name(loop_name)), Tx(Emit), Nx(Node::Term(body))] => {
					Node::Term(ParsedTerm::Emit { loop_name, argument: Box::new(body) })
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::SmallValue => {
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
				[Tx(OpenParen), Nx(Node::ValueList(list)), Tx(CloseParen)] => {
					Node::Term(ParsedTerm::Tuple(list))
				},
				[Nx(Node::Term(tuple)), Tx(Period), Tx(IntegerLiteral(integer))] => {
					if let Some(index) = usize::try_from(integer).ok() {
						Node::Term(ParsedTerm::Projection { tuple: Box::new(tuple), index })
					} else {
						Node::Fail
					}
				},
				[Tx(OpenOrtho), Nx(Node::Term(term)), Tx(CloseOrtho)] => {
					Node::Term(term)
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::ValueList => {
			match_slice! { pattern;
				[] => Node::ValueList(Vec::new()),
				[Nx(Node::Term(term))] => Node::ValueList(Vec::from([term])),
				[Nx(Node::ValueList(list)), Tx(Comma), Nx(Node::Term(term))] => {
					let mut list = list;
					list.push(term);
					Node::ValueList(list)
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::IntrinsicInvocation => {
			match_slice! { pattern;
				[Tx(Intrinsic(intrinsic))] => Node::Term(ParsedTerm::IntrinsicInvocation {intrinsic, arguments: Vec::new()}),
				[Nx(Node::Term(ParsedTerm::IntrinsicInvocation {intrinsic, arguments})), Nx(Node::Term(term))] => {
					let mut arguments = arguments;
					arguments.push(term);
					Node::Term(ParsedTerm::IntrinsicInvocation {intrinsic, arguments})
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
				[Tx(Asterisk), Tx(OpenParen), Nx(Node::TypeList(list)), Tx(CloseParen)] => {
					Node::Type(ParsedType::Product(list))
				},
				[Tx(OpenOrtho), Nx(Node::Type(ty)), Tx(CloseOrtho)] => {
					Node::Type(ty)
				},
				_ => Node::Fail,
			}
		},
		Nonterminal::TypeList => {
			match_slice! { pattern;
				[] => Node::TypeList(Vec::new()),
				[Nx(Node::Type(ty))] => Node::TypeList(Vec::from([ty])),
				[Nx(Node::TypeList(list)), Tx(Comma), Nx(Node::Type(ty))] => {
					let mut list = list;
					list.push(ty);
					Node::TypeList(list)
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
				[@LongValue],
				[!Name, !Bicolon, @DelimitedValue, @Value],      // Assignment
				[@LongValue, !EqualsQuestion, @LongValue], // Equality query
				[@DelimitedValue, !Question, @Cases],             // Case split
			]
			LongValue => [
				[@AppliedValue],
				[@IntrinsicInvocation],
			]
			AppliedValue => [
				[@DelimitedValue],
				[@AppliedValue, @DelimitedValue], // Function Application
			]
			DelimitedValue => [
				[@SmallValue],
				[!OpenCurly, !Name, @Type, !CloseCurly, !Arrow, @DelimitedType, @DelimitedValue],   // Lambda binding
				[!OpenCurly, !Name, @Type, !CloseCurly, @DelimitedValue],   // Lambda binding
				[!OpenCurly, !Name, !Arrova, !CloseCurly, @DelimitedValue], // Mu binding
				[!OpenCurly, !Name, !Ampersand, !CloseCurly, @DelimitedValue, !OpenCurly, !Name, !CloseCurly, !Arrow, @DelimitedType, @DelimitedValue], // Loop
				[!Name, !Step, @DelimitedValue],
				[!Name, !Emit, @DelimitedValue],
			]
			SmallValue => [
				[!IntegerLiteral],
				[!Name],
				[!OpenParen, @ValueList, !CloseParen],
				// FIXME: Use natural literals instead.
				[@SmallValue, !Period, !IntegerLiteral],
				[!OpenOrtho, @Value, !CloseOrtho],
			]
			ValueList => [
				[],
				[@Value],
				[@ValueList, !Comma, @Value],
			]
			IntrinsicInvocation => [
				[!Intrinsic],
				[@IntrinsicInvocation, @DelimitedValue],
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
				[!Asterisk, !OpenParen, @TypeList, !CloseParen],
				[!OpenOrtho, @Type, !CloseOrtho],
			]
			TypeList => [
				[],
				[@Type],
				[@TypeList, !Comma, @Type],
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

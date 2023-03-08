// FIXME: When available, use min_generic_const_exprs.
// FIXME: This feature requires the use of forwards-incompatible const bounds.
// FIXME: When possible, remove this feature flag entirely.
// REASON: This is used to enable types being generic on associated constants given by trait implementations of their type parameters.
#![feature(generic_const_exprs)]
// FIXME: Track https://github.com/rust-lang/rust/pull/101179: this may be replaced.
// REASON: This is used as a convenient interface for working with uninitialized arrays. Not entirely sure why the API designers are undecided on this one.
#![feature(maybe_uninit_uninit_array_transpose)]
// FIXME: Track relevant issues: this may be replaced.
// REASON: This is used as a way for a declarative macro to easily obtain the number of variants of an enum without having to parse the enum itself.
#![feature(variant_count)]
#![feature(never_type)]
// TODO: Remove this.
// REASON: Reduces warning noise while prototyping.
#![allow(dead_code, unused_macros)]

#[macro_use]
extern crate maplit;

#[path = "generator/_.rs"]
mod generator;
#[path = "interpreter/_.rs"]
mod interpreter;
#[path = "parser/_.rs"]
mod parser;
#[path = "translator/_.rs"]
mod translator;
#[path = "util/_.rs"]
mod util;

use std::sync::Arc;

use generator::*;
use grammar::*;
use interpreter::base::interpret_base;
use parser::{
	lexer::Lexer,
	parser::{Node, Parser},
};
use translator::elaborator::{elaborate, BaseType, Context};
use util::*;

use crate::interpreter::base::{BaseEnvironment, BaseValue};

fn main() {
	let lexer = Lexer::new(include_str!("../examples/fib.tetra"));

	let parser = Parser::new().unwrap();

	let expression = parser.parse(lexer).unwrap();

	if let Node::Term(parsed_term) = expression {
		let elaborated_expression = elaborate(
			Context::new(vec![(
				"add".to_owned(),
				BaseType::Power {
					domain: Box::new(BaseType::Integer),
					codomain: Box::new(BaseType::Power {
						domain: Box::new(BaseType::Integer),
						codomain: Box::new(BaseType::Integer),
					}),
				},
			)]),
			parsed_term,
			None,
		)
		.unwrap();

		let interpreted_value = interpret_base(
			elaborated_expression,
			BaseEnvironment::new(vec![(
				"add".to_owned(),
				BaseValue::Function(Arc::new(|value_0| match value_0 {
					BaseValue::Integer(x) => Some(BaseValue::Function(Arc::new(move |value_1| match value_1 {
						BaseValue::Integer(y) => Some(BaseValue::Integer(x + y)),
						_ => None,
					}))),
					_ => None,
				})),
			)]),
		);

		println!("{:#?}", interpreted_value);
	} else {
		panic!("Not a term");
	}
}

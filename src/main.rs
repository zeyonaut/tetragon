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

#[macro_use(btreemap, btreeset)]
extern crate maplit;

#[path = "generator/_.rs"]
mod generator;
#[path = "interpreter/_.rs"]
mod interpreter;
#[path = "parser/_.rs"]
mod parser;
#[path = "translator/_.rs"]
mod translator;
#[path = "utility/_.rs"]
mod utility;

use std::time::Instant;

use generator::*;
use grammar::*;
use parser::{
	lexer::Lexer,
	parser::{Node, Parser},
};
use translator::{hoister::hoist, label::LabelGenerator, sequentializer::sequentialize};
use utility::*;

use crate::{
	interpreter::{
		base::{evaluate_base, interpret_base, BaseEnvironment, BaseValue, BaseVariable},
		flow::pretty_print_program,
	},
	translator::{elaborator::elaborate_program, nasm_win64},
};

fn main() {
	let args = std::env::args().collect::<Vec<_>>();

	let file_path = args.get(1).expect("Expected file path as first argument.");

	let output_path = args.get(2);

	let file_contents = std::fs::read_to_string(file_path).expect("Could not read specified file.");

	let lexer = Lexer::new(&file_contents);

	let parser = Parser::new().unwrap();

	let expression = parser.parse(lexer).unwrap();

	if let Node::Term(parsed_term) = expression {
		let mut symbol_generator = LabelGenerator::new();

		let term = elaborate_program(parsed_term, &mut symbol_generator).expect("Elaboration failed.");

		let program = hoist(term, symbol_generator);

		let program = sequentialize(program);

		println!("{}", pretty_print_program(&program));

		let program = nasm_win64::emit_program(program);

		if let Some(program) = program {
			std::fs::write(output_path.expect("expected output argument"), program).expect("failed to write output");
		}
	} else {
		panic!("Not a term");
	}
}

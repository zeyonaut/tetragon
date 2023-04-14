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
#[macro_use(hashmap)]
extern crate halfbrown;

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

use generator::*;
use grammar::*;
use parser::{
	lexer::Lexer,
	parser::{Node, Parser},
};
use translator::label::LabelGenerator;
use utility::*;

use crate::{
	interpreter::base::{evaluate_base, interpret_base, BaseEnvironment, BaseValue, BaseVariable},
	translator::{
		cps::{convert_program_to_cps, convert_type_to_cps},
		elaborator::elaborate_program,
		hoister::hoist_program,
		nasm_win64,
	},
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

		let (elaborated_term, _) = elaborate_program(parsed_term, &mut symbol_generator).expect("Elaboration failed.");

		// println!("Elaborated term: {:#?}", elaborated_term);

		use std::time::Instant;

		let now = Instant::now();

		//let interpreted_value = evaluate_base(elaborated_term.clone());

		let elapsed = now.elapsed();

		println!("Elapsed (Base): {:.2?}", elapsed);

		//println!("Interpreted value: {:#?}", interpreted_value);

		let cypress_ty = convert_type_to_cps(elaborated_term.ty());
		let cypress_term =
			convert_program_to_cps(elaborated_term, &mut symbol_generator).expect("Failed to convert base term to CPS.");

		// println!("CPS-converted term: {:#?}", cypress_term);

		let now = Instant::now();

		//let cypress_value = cypress_term.clone().evaluate(symbol_generator.clone());

		let elapsed = now.elapsed();

		println!("Elapsed (CPS): {:.2?}", elapsed);

		//println!("CPS-converted value: {:#?}", cypress_value);

		let firefly_program = hoist_program(cypress_term, cypress_ty, &mut symbol_generator);

		//println!("Hoisted program: {:#?}", firefly_program);

		let now = Instant::now();

		//let firefly_value = firefly_program.clone().evaluate();

		let elapsed = now.elapsed();

		println!("Elapsed (Firefly): {:#?}", elapsed);
		//println!("Firefly value: {:#?}", firefly_value);

		let program = nasm_win64::emit_program(firefly_program).map(nasm_win64::emit_assembly);

		if let Some(program) = program {
			std::fs::write(output_path.expect("expected output argument"), program).expect("failed to write output");
		}
	} else {
		panic!("Not a term");
	}
}

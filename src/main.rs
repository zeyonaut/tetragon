// FIXME: When available, use min_generic_const_exprs.
// FIXME: This feature requires the use of forwards-incompatible const bounds.
// FIXME: When possible, remove this feature flag entirely.
// REASON: This is used to enable types being generic on associated constants given by trait implementations of their type parameters.
#![feature(generic_const_exprs)]
#![feature(adt_const_params)]
// FIXME: Track https://github.com/rust-lang/rust/pull/101179: this may be replaced.
// REASON: This is used as a convenient interface for working with uninitialized arrays. Not entirely sure why the API designers are undecided on this one.
#![feature(maybe_uninit_uninit_array_transpose)]
// FIXME: Track relevant issues: this may be replaced.
// REASON: This is used as a way for a declarative macro to easily obtain the number of variants of an enum without having to parse the enum itself.
#![feature(variant_count)]
// TODO: Remove this.
// REASON: Reduces warning noise while prototyping.
#![allow(dead_code, unused_imports, unused_macros)]

#[macro_use]
extern crate maplit;

#[path = "generator/_.rs"]
mod generator;
#[path = "parser/_.rs"]
mod parser;
#[path = "util/_.rs"]
mod util;

use std::mem::size_of;

use enum_iterator::Sequence;
use generator::*;
use grammar::*;
use lexer::Lexer;
use parser::*;
use pow::{impl_downset_for_repr_enum, pow};
use slice::slice;
use util::*;

fn main() {
	let lexer = Lexer::new(include_str!("../tetra/fib.tetra"));

	#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
	#[repr(u8)]
	enum Nonterminal {
		Value,
		DelimitedValue,
		AppliedValue,
		LambdaBinding,
		MuBinding,
		Assignment,
		Type,
		DelimitedType,
		Cases,
	}

	impl_downset_for_repr_enum![Nonterminal ~ u8];

	use lexer::Terminal::*;
	use Nonterminal::*;

	let grammar = grammar![
		Value;
		Value => [
			[@Assignment, @Value],
			[@AppliedValue, !EqualsQuestion, @AppliedValue],
			[@AppliedValue],
			[@DelimitedValue, !Question, @Cases]
		]
		AppliedValue => [
			[@DelimitedValue],
			[@AppliedValue, @DelimitedValue], // Function Application
		]
		DelimitedValue => [
			[!IntegerLiteral],
			[!Name],
			[!OpenOrtho, @Value, !CloseOrtho],
			[@LambdaBinding, @DelimitedValue],
			[@MuBinding, @DelimitedValue],
		]
		LambdaBinding => [
			[!OpenCurly, !Name, @Type, !CloseCurly],
		]
		MuBinding => [
			[!OpenCurly, !Name, !Arrova, !CloseCurly],
		]
		Assignment => [
			[!Name, !Bicolon, @DelimitedValue],
		]
		Cases => [
			[],
			[@Cases, !Name, !Bar, @DelimitedValue],
		]
		Type => [
			[@DelimitedType],
			[@DelimitedType, !Arrow, @Type],
		]
		DelimitedType => [
			[!Name],
		]
	];

	let lalr1_parser = lalr1::Parser::new(&grammar).unwrap();

	#[derive(Debug)]
	enum Expr {
		Any,
	}

	lalr1_parser.parse(lexer, |_| Expr::Any).unwrap();
}

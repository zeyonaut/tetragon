// FIXME: When available, use min_generic_const_exprs.
// FIXME: This feature requires the use of forwards-incompatible const bounds.
// FIXME: When possible, remove this feature flag entirely.
// REASON: This is used to enable types being generic on associated constants given by trait implementations of their type parameters.
#![feature(generic_const_exprs)]
// FIXME: Track https://github.com/rust-lang/rust/pull/101179: this may be replaced.
// REASON: This is used as a convenient interface for working with uninitialized arrays. Not entirely sure why the API designers are undecided on this one.
#![feature(maybe_uninit_uninit_array_transpose)]
// FIXME: Track relevant issues: this may be replaced.
// REASON: This is used as a way for a declarative macro to easily get obtain number of variants of an enum without having to parse the enum itself.
#![feature(variant_count)]
// TODO: Remove this.
// REASON: Reduces warning noise while prototyping.
#![allow(dead_code, unused_variables, unused_imports, unused_macros)]

#[macro_use]
extern crate maplit;

mod util;
#[macro_use]
mod pow;
#[macro_use]
mod slice;

mod lexer;

#[macro_use]
mod grammar;
#[macro_use]
mod lr0;
#[macro_use]
mod lalr1;

use std::mem::size_of;

use enum_iterator::Sequence;
use grammar::*;

fn main() {
	#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
	#[repr(u8)]
	enum Terminal {
		Id,
		Equals,
		Star,
	}

	impl_downset_for_repr_enum![Terminal ~ u8];

	use Terminal::*;

	#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
	#[repr(u8)]
	enum Nonterminal {
		S,
		L,
		R,
	}

	impl_downset_for_repr_enum![Nonterminal ~ u8];

	use Nonterminal::*;

	let grammar = grammar![
		S;
		S => [
			[@L, !Equals, @R],
			[@R],
		],
		L => [
			[!Star, @R],
			[!Id],
		],
		R => [
			[@L]
		],
	];

	let lalr1_parser = lalr1::Parser::new(&grammar);

	println!("{:#?}", lalr1_parser);
}

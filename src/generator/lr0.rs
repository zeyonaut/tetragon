use std::{collections::BTreeSet, fmt::Debug};

use enum_iterator::{all, Sequence};

use crate::{fix::fix, grammar::*, pow::*};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Item<N, T> {
	production: Production<N, T>,
	symbol_index: usize,
}

impl<N: Debug + Downset, T: Debug> Debug for Item<N, T> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.write_fmt(format_args!(
			"{:?} -> {} in {:?}",
			self.production.target(),
			self.symbol_index,
			self.production.pattern()
		))
	}
}

impl<N: Downset, T> Item<N, T>
where
	[(); N::SIZE]:,
{
	pub fn new(production: Production<N, T>) -> Self {
		Self {
			symbol_index: 0,
			production,
		}
	}

	pub fn new_at(production: Production<N, T>, symbol_index: usize) -> Self {
		Self {
			symbol_index: symbol_index,
			production,
		}
	}

	pub fn production(&self) -> &Production<N, T> {
		&self.production
	}

	pub fn target(&self) -> Option<&N>
	where
		N: Copy,
	{
		self.production.target()
	}

	pub fn postpattern(&self) -> &[Symbol<N, T>]
	where
		N: Copy,
	{
		&self.production.pattern()[self.symbol_index..]
	}

	pub fn requirement(&self) -> Option<Symbol<N, T>>
	where
		N: Copy,
		T: Copy,
	{
		self.postpattern().get(0).copied()
	}

	pub fn successor(&self) -> Self
	where
		N: Copy,
		T: Copy,
	{
		Self {
			production: self.production.clone(),
			symbol_index: self.symbol_index.wrapping_add(1),
		}
	}

	pub fn skip(&self, n: usize) -> Self
	where
		N: Copy,
		T: Copy,
	{
		Self {
			production: self.production.clone(),
			symbol_index: self.symbol_index.wrapping_add(n),
		}
	}
}

macro_rules! lr0_item {
	// Auxilliary: Parse a target which is the start symbol.
	[@target ?] => {
		::core::option::Option::None
	};

	// Auxilliary: Parse a target which is not the start symbol.
	[@target $target:expr] => {
		::core::option::Option::Some($target)
	};

	// Auxilliary: Parse a symbol marked as terminal.
	[@symbol ! $symbol:expr] => {
		$crate::grammar::Symbol::Terminal($symbol)
	};

	// Auxilliary: Parse a symbol marked as nonterminal.
	[@symbol @ $symbol:expr] => {
		$crate::grammar::Symbol::Nonterminal($symbol)
	};

	// Entry
	[$cursor:expr; $target:tt -> $($kind:tt $symbol:expr),* $(,)?] => ({
		use $crate::utility::slice::slice;
		$crate::lr0::Item::new_at($crate::grammar::Production::new(lr0_item![@target $target], slice![$(lr0_item![@symbol $kind $symbol]),*]), $cursor)
	});
}

// TODO: Maybe use some sort of typestate to distinguish between cokernels, kernels, and arbitrary states?
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct State<N: Downset, T> {
	pub items: BTreeSet<Item<N, T>>,
}

impl<N: Downset, T> State<N, T>
where
	[(); N::SIZE]:,
{
	pub fn new(items: BTreeSet<Item<N, T>>) -> Self {
		Self { items }
	}

	pub fn items(&self) -> &BTreeSet<Item<N, T>> {
		&self.items
	}

	pub fn close(&self, grammar: &Grammar<N, T>) -> Self
	where
		N: Copy + Eq + Ord,
		T: Copy + Eq + Ord,
	{
		Self {
			items: fix(self.items.clone(), |items| {
				let mut new_items = items.clone();
				for item in items {
					if let Some(Symbol::Nonterminal(successor)) = item.requirement() {
						for production in grammar.productions_of(successor) {
							new_items.insert(Item::new(production));
						}
					}
				}
				new_items
			}),
		}
	}

	pub fn coclose(&self) -> Self
	where
		N: Copy + Ord,
		T: Copy + Ord,
	{
		Self {
			items: self
				.items
				.iter()
				.filter(|item| item.target().is_none() || item.symbol_index > 0)
				.cloned()
				.collect(),
		}
	}

	pub fn step(&self, grammar: &Grammar<N, T>, encounter: Symbol<N, T>) -> Self
	where
		N: Copy + PartialEq + Eq + Ord,
		T: Copy + PartialEq + Eq + Ord,
	{
		Self::new(
			self.items
				.iter()
				.filter(|item| item.requirement() == Some(encounter))
				.map(|item| item.successor())
				.collect(),
		)
		.close(grammar)
	}

	pub fn canonical_cokernels(grammar: &Grammar<N, T>) -> BTreeSet<Self>
	where
		N: Sequence + Copy + PartialEq + Eq + Ord + Debug,
		T: Sequence + Copy + PartialEq + Eq + Ord + Debug,
	{
		fix(
			btreeset![State::new(btreeset![Item::new(grammar.start_production())]).close(grammar)],
			|collection| {
				let mut new_collection = collection.clone();
				for set in collection {
					for symbol in all::<Symbol<N, T>>() {
						let next_set = set.step(grammar, symbol);
						if !next_set.items.is_empty() {
							new_collection.insert(next_set);
						}
					}
				}
				new_collection
			},
		)
	}

	pub fn canonical_kernels(grammar: &Grammar<N, T>) -> BTreeSet<Self>
	where
		N: Sequence + Copy + PartialEq + Eq + Ord + Debug,
		T: Sequence + Copy + PartialEq + Eq + Ord + Debug,
	{
		Self::canonical_cokernels(grammar)
			.into_iter()
			.map(|cokernel| cokernel.coclose())
			.collect()
	}
}

mod tests {
	#[cfg(test)]
	use enum_iterator::Sequence;

	#[cfg(test)]
	use crate::{grammar::*, lr0::*};

	// Example 4.40, p. 244
	#[test]
	fn test_lr0_closure() {
		#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
		enum Terminal {
			Plus,
			Star,
			Open,
			Close,
			Id,
		}

		use Terminal::*;

		#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
		#[repr(u8)]
		enum Nonterminal {
			E,
			Q,
			F,
		}

		impl_downset_for_repr_enum![Nonterminal ~ u8];

		use Nonterminal::*;

		let grammar = grammar![
			E;
			E => [
				[@E, !Plus, @Q],
				[@Q],
			],
			Q => [
				[@Q, !Star, @F],
				[@F],
			],
			F => [
				[!Open, @E, !Close],
				[!Id],
			]
		];

		let state = State::new(btreeset![Item::new(grammar.start_production())]);

		let cokernel = state.close(&grammar);

		assert_eq!(
			cokernel,
			State::new(btreeset![
				lr0_item![0; E -> @E, !Plus, @Q],
				lr0_item![0; ? -> @E],
				lr0_item![0; E -> @Q],
				lr0_item![0; Q -> @Q, !Star, @F],
				lr0_item![0; Q -> @F],
				lr0_item![0; F -> !Open, @E, !Close],
				lr0_item![0; F -> !Id],
			]),
		);
	}

	// Example 4.61, p. 271
	#[test]
	fn test_lr0_coclosure() {
		#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
		enum Terminal {
			Id,
			Equals,
			Star,
		}

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

		let cokernels: BTreeSet<_> = State::canonical_cokernels(&grammar);

		let kernels: BTreeSet<_> = cokernels.iter().map(|cokernel| cokernel.coclose()).collect();

		#[rustfmt::skip]
		assert_eq!(
			kernels,
			btreeset![
				State::new(btreeset![lr0_item![0; ? -> @S]]),
				State::new(btreeset![lr0_item![1; ? -> @S]]),
				State::new(btreeset![
					lr0_item![1; S -> @L, !Equals, @R], 
					lr0_item![1; R -> @L],
				]),
				State::new(btreeset![lr0_item![1; S -> @R]]),
				State::new(btreeset![lr0_item![1; L -> !Star, @R]]),
				State::new(btreeset![lr0_item![1; L -> !Id]]),
				State::new(btreeset![lr0_item![2; S -> @L, !Equals, @R]]),
				State::new(btreeset![lr0_item![2; L -> !Star, @R]]),
				State::new(btreeset![lr0_item![1; R -> @L]]),
				State::new(btreeset![lr0_item![3; S -> @L, !Equals, @R]]),
			]
		);
	}
}

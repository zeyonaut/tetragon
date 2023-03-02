use std::{cmp::min, collections::BTreeSet};

use enum_iterator::{all, Sequence};

use crate::util::{fix::fix, pow::*, slice::*};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Sequence)]
pub enum Symbol<N, T> {
	Nonterminal(N),
	Terminal(T),
}

#[derive(Debug)]
pub struct Grammar<N, T>
where
	N: Downset,
	[(); N::SIZE]:,
{
	start: N,
	patterns_of: Pow<N, Slice<Slice<Symbol<N, T>>>>,
	start_pattern: [Symbol<N, T>; 1],
	initials_of: Pow<N, BTreeSet<Option<T>>>,
}

impl<N: Downset, T> Grammar<N, T>
where
	N: Eq + Copy,
	T: Ord + Copy,
	[(); N::SIZE]:,
{
	pub fn new(start: N, patterns_of: Pow<N, Slice<Slice<Symbol<N, T>>>>) -> Self {
		// Compute the initials_of map (FIRST sets).
		let initials_of = fix(
			&pow! {
				_ => BTreeSet::from([]),
			},
			|initials_of| {
				let mut new_initials_of = initials_of.clone();

				for (nonterm, patterns) in patterns_of.iter() {
					let initials_of = initials_of;
					'patterns: for pattern in patterns.iter() {
						for symbol in pattern.iter() {
							match symbol {
								Symbol::Terminal(terminal) => {
									new_initials_of[nonterm].insert(Some(*terminal));
									continue 'patterns;
								},
								Symbol::Nonterminal(nonterminal) => {
									new_initials_of[nonterm]
										.extend(initials_of[*nonterminal].clone().into_iter().filter(Option::is_some));
									if !initials_of[(*nonterminal)].contains(&None) {
										continue 'patterns;
									}
								},
							}
						}
						new_initials_of[nonterm].insert(None);
					}
				}
				new_initials_of
			},
		);

		Self {
			start,
			patterns_of,
			start_pattern: [Symbol::Nonterminal(start)],
			initials_of,
		}
	}

	pub fn start(&self) -> N {
		self.start
	}

	pub fn productions_of<'g>(&'g self, target: N) -> impl Iterator<Item = Production<N, T>> + 'g {
		self.patterns_of[target].iter().map(move |pattern| Production {
			target: Some(target),
			pattern: pattern.clone(),
		})
	}

	pub fn start_production<'g>(&'g self) -> Production<N, T> {
		Production {
			target: None,
			pattern: slice![Symbol::Nonterminal(self.start)],
		}
	}

	// Compute the set of terminals that may occur at the beginning of a sequence.
	pub fn initials_of_sequence<'a>(
		&self,
		sequence: impl IntoIterator<Item = &'a Symbol<N, T>>,
		sentinel: Option<T>,
	) -> BTreeSet<Option<T>>
	where
		T: 'a,
		N: 'a,
	{
		let mut initials = BTreeSet::new();

		for symbol in sequence {
			match symbol {
				Symbol::Terminal(terminal) => {
					initials.insert(Some(*terminal));
					return initials;
				},
				Symbol::Nonterminal(nonterminal) => {
					initials.extend(self.initials_of[*nonterminal].clone().into_iter().filter(Option::is_some));
					if !self.initials_of[*nonterminal].contains(&None) {
						return initials;
					}
				},
			}
		}
		initials.insert(sentinel);

		initials
	}
}

macro_rules! grammar {
	// Auxilliary: Parse a symbol marked as terminal.
	[@symbol ! $symbol:expr] => {
		$crate::grammar::Symbol::Terminal($symbol)
	};

	// Auxilliary: Parse a symbol marked as nonterminal.
	[@symbol @ $symbol:expr] => {
		$crate::grammar::Symbol::Nonterminal($symbol)
	};

	// Entry: Parse a list of grammar rules.
	[$start:expr; $($key:pat => [$([$($kind:tt $symbol:expr),* $(,)?]),* $(,)?] $(,)?)*] => (
		$crate::generator::grammar::Grammar::new($start, pow! {
			$($key => slice![$(slice![$(grammar![@symbol $kind $symbol]),*]),*]),*
		})
	);
}
pub(crate) use grammar;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Production<N, T> {
	// TODO: I'm not entirely convinced that this needs to accomodate the start symbol.
	target: Option<N>,
	pattern: Slice<Symbol<N, T>>,
}

impl<N: Downset, T> Production<N, T> {
	pub(crate) fn new(target: Option<N>, pattern: Slice<Symbol<N, T>>) -> Self {
		Self { target, pattern }
	}

	pub fn target(&self) -> Option<&N> {
		self.target.as_ref()
	}

	pub fn pattern<'g>(&'g self) -> &'g [Symbol<N, T>] {
		&self.pattern
	}
}

use std::{
	collections::{BTreeMap, BTreeSet},
	error::Error,
	fmt::Debug,
	iter::Peekable,
};

use thiserror::Error;

use crate::{
	fix::fix,
	grammar::*,
	lexer::LexError,
	pow::*,
	slice::{slice, Slice},
	terminal::HasTerminal,
	*,
};

// An LR(1) item is an LR(0) item with an additional sentinel;
// Successful completion requires that the sentinel is observed.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Item<N: Downset, T> {
	item: lr0::Item<N, T>,
	sentinel: Option<T>,
}

impl<N: Debug + Downset, T: Debug> Debug for Item<N, T> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		f.write_fmt(format_args!("{:?} | {:?}", self.item, self.sentinel))
	}
}

impl<N: Downset, T> Item<N, T> {
	pub fn new(item: lr0::Item<N, T>, sentinel: Option<T>) -> Self {
		Self { item, sentinel }
	}

	pub fn item(&self) -> &lr0::Item<N, T> {
		&self.item
	}

	pub fn sentinel(&self) -> Option<T>
	where
		T: Copy,
	{
		self.sentinel
	}

	pub fn successor(&self) -> Self
	where
		N: Copy,
		T: Copy,
		[(); N::SIZE]:,
	{
		Self {
			item: self.item.successor(),
			sentinel: self.sentinel,
		}
	}
}

macro_rules! lr1_item {
	// Auxilliary: Parse a target which is the start symbol or a sentinel which is the end symbol.
	[@target ?] => {
		::core::option::Option::None
	};

	// Auxilliary: Parse a target which is not the start symbol or a sentinel which is not the end symbol.
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
	[$cursor:expr; $target:tt -> $($kind:tt $symbol:expr),* $(,)?; $sentinel:tt] => (
		$crate::generator::lalr1::Item::new($crate::generator::lr0::Item::new_at($crate::generator::grammar::Production::new(lr1_item![@target $target], slice![$(lr1_item![@symbol $kind $symbol]),*]), $cursor), lr1_item![@target $sentinel])
	);
}

struct State<N: Downset, T> {
	items: BTreeSet<Item<N, T>>,
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

	// Compute the closure of a set of LR(1) items.
	// The closure is the fixed point of the image
	// of the function that takes an 'item', that is,
	// a task, and adds all subtasks of it.
	pub fn elaborate(&self, grammar: &Grammar<N, T>) -> Self
	where
		N: Copy + Eq + Ord,
		T: Copy + Eq + Ord,
	{
		Self {
			items: fix(&self.items, |items| {
				let mut new_items = items.clone();
				for item in items {
					if let Some(Symbol::Nonterminal(successor)) = item.item().requirement() {
						for new_sentinel in grammar.initials_of_sequence(&item.item().postpattern()[1..], item.sentinel()) {
							for new_production in grammar.productions_of(successor) {
								new_items.insert(Item::new(lr0::Item::new(new_production), new_sentinel));
							}
						}
					}
				}
				new_items
			}),
		}
	}

	// Compute GOTO
	pub fn step(&self, grammar: &Grammar<N, T>, encounter: Symbol<N, T>) -> Self
	where
		N: Copy + PartialEq + Eq + Ord,
		T: Copy + PartialEq + Eq + Ord,
	{
		Self::new(
			self.items
				.iter()
				.filter(|item| item.item.requirement() == Some(encounter))
				.map(|item| item.successor())
				.collect(),
		)
		.elaborate(grammar)
	}
}

pub fn kernels<N, T>(grammar: &Grammar<N, T>) -> BTreeSet<BTreeSet<Item<N, T>>>
where
	N: Copy + Eq + Ord + Downset + Sequence + Debug,
	T: Copy + Eq + Ord + Sequence + Debug,
	[(); N::SIZE]:,
{
	// Step 0: Compute LR0 Kernels
	let lr0_kernels: BTreeSet<BTreeSet<lr0::Item<N, T>>> = lr0::State::canonical_spans(grammar)
		.into_iter()
		.map(|span| span.summarize().items)
		.collect();

	// Step 2: Determine lookaheads (4.62)

	// Spontaneous lookaheads:
	let mut generated_sentinels: BTreeMap<(BTreeSet<lr0::Item<N, T>>, lr0::Item<N, T>), BTreeSet<Option<T>>> = btreemap![
		(btreeset![lr0::Item::new(grammar.start_production())], lr0::Item::new(grammar.start_production())) => btreeset![None]
	];

	// Propagated lookaheads:
	let mut sentinel_recipients: BTreeMap<
		(BTreeSet<lr0::Item<N, T>>, lr0::Item<N, T>),
		BTreeSet<(BTreeSet<lr0::Item<N, T>>, lr0::Item<N, T>)>,
	> = btreemap![];

	for lr0_kernel in &lr0_kernels {
		for lr0_item in lr0_kernel {
			// We elaborate to see which items in the span will generate/propagate lookaheads to other states.
			let lalr1_testing_span = State::new(btreeset![Item::new(lr0_item.clone(), None)]).elaborate(grammar);
			for lalr1_testing_item in lalr1_testing_span.items() {
				if let Some(requirement) = lalr1_testing_item.item().requirement() {
					// This computes GOTO(I, X).
					let successor_lr0_kernel = lr0::State::new(lr0_kernel.clone())
						.elaborate(grammar)
						.step(grammar, requirement)
						.summarize();

					let successor_lr0_item = lalr1_testing_item.item().successor();

					if let Some(generated_sentinel) = lalr1_testing_item.sentinel() {
						generated_sentinels
							.entry((successor_lr0_kernel.items, successor_lr0_item))
							.or_default()
							.insert(Some(generated_sentinel));
					} else {
						sentinel_recipients
							.entry((lr0_kernel.clone(), lr0_item.clone()))
							.or_default()
							.insert((successor_lr0_kernel.items, successor_lr0_item));
					}
				}
			}
		}
	}

	// Propagate lookaheads.
	let sentinels_of = fix(&generated_sentinels, |sentinels| {
		let mut new_sentinels = sentinels.clone();
		for lr0_kernel in &lr0_kernels {
			for lr0_item in lr0_kernel {
				let donor = (lr0_kernel.clone(), lr0_item.clone());
				if let Some(donor_sentinels) = sentinels.get(&donor) {
					for recipient in sentinel_recipients.entry(donor.clone()).or_default().iter() {
						new_sentinels
							.entry(recipient.clone())
							.or_default()
							.extend(donor_sentinels.iter());
					}
				}
			}
		}
		new_sentinels
	});

	// Extract kernels.
	let mut lalr1_kernels_of: BTreeMap<BTreeSet<lr0::Item<N, T>>, BTreeSet<Item<N, T>>> = btreemap![];

	for ((lr0_kernel, lr0_item), sentinels) in sentinels_of {
		lalr1_kernels_of
			.entry(lr0_kernel)
			.or_default()
			.extend(sentinels.into_iter().map(|sentinel| Item::new(lr0_item.clone(), sentinel)));
	}

	let lalr1_kernels: BTreeSet<BTreeSet<Item<N, T>>> = lalr1_kernels_of.into_values().collect();

	lalr1_kernels
}

#[derive(Error, Debug, PartialEq)]
pub enum GenerateParserError {
	#[error("encountered reduce-reduce ambiguity when generating LALR(1) parser")]
	ReduceReduce,
	#[error("encountered shift-reduce ambiguity when generating LALR(1) parser")]
	ShiftReduce,
	// I'm pretty sure shift-shift ambiguities can't be encountered, but this error is included for completion.
	#[error("encountered shift-shift ambiguity when generating LALR(1) parser")]
	ShiftShift,
	// I'm also pretty sure this can never occur, but I'm including it anyway.
	#[error("encountered missing state when generating LALR(1) parser")]
	MissingState,
}

#[derive(Error, Debug)]
pub enum ParseError<X: Error> {
	#[error(transparent)]
	LexError(#[from] X),
	#[error("ran out of states unexpectedly")]
	DepletedStateStack,
	#[error("a state in the state stack was invalid (this should never occur!)")]
	InvalidState,
	#[error("encountered a reduce action with a start target (this should never occur!)")]
	EarlyAcceptance,
	#[error("encountered unexpected terminal while parsing")]
	UnexpectedTerminal,
	#[error("encountered unexpected nonterminal while parsing")]
	UnexpectedNonterminal,
	#[error("encountered unexpected end of input while parsing")]
	UnexpectedEndOfInput,
	#[error("encountered production with pattern of greater length than current state or expression stack")]
	OverlongReduction,
	#[error("parsing finished without reducing start production")]
	FailedReturn,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Action<N, T> {
	Reduce(Production<N, T>),
	Shift(usize),
}

#[derive(Debug)]
pub struct Table<N: Downset, T: Downset>
where
	[(); T::SIZE]:,
	[(); N::SIZE]:,
{
	state: BTreeSet<Item<N, T>>,
	reduction: Option<Production<N, T>>,
	action: Pow<T, Option<Action<N, T>>>,
	goto: Pow<N, Option<usize>>,
}

#[derive(Debug)]
pub struct Parser<N: Downset, T: Downset>
where
	[(); T::SIZE]:,
	[(); N::SIZE]:,
{
	table_by_state: Vec<Table<N, T>>,
	initial_state: usize,
}

impl<N: Downset, T: Downset> Parser<N, T>
where
	[(); T::SIZE]:,
	[(); N::SIZE]:,
{
	// TODO: This code is really hard to read and should be cleaned up/refactored.
	pub fn new(grammar: &Grammar<N, T>) -> Result<Self, GenerateParserError>
	where
		N: Copy + Eq + Ord + Downset + Sequence + Debug,
		T: Copy + Eq + Ord + Sequence + Debug,
	{
		use Action::*;
		use GenerateParserError::*;
		let lalr1_bases = kernels(grammar);

		let lalr1_spans: Vec<_> = lalr1_bases
			.into_iter()
			.map(|lalr1_basis| State::new(lalr1_basis).elaborate(grammar).items)
			.collect();

		let mut index_of_basis = BTreeMap::new();
		for (index, span) in lalr1_spans.clone().into_iter().enumerate() {
			// TODO: To prevent bugs, turn instances of span_to_basis into a single function on states! Maybe even LR(1) kernels, if that concept exists...
			// Yeah, that concept exists: check p. 270. 4.7.5.
			// So, convert to an LR(1) kernel, then convert to an LR(0) kernel?
			let basis: BTreeSet<lr0::Item<N, T>> = lr0::State::new(span.iter().map(Item::item).cloned().collect())
				.summarize()
				.items;
			index_of_basis.insert(basis, index);
		}
		let index_of_basis = index_of_basis;

		let mut action_tables = Vec::new();
		let mut goto_tables = Vec::new();
		let mut reductions = Vec::new();
		for lalr1_span in lalr1_spans.clone() {
			// Construct the ACTION table.
			// NOTE: Explicit type hinting is required due to type inference bug in generic_const_exprs.
			// TODO: Might be a good idea to construct a minimal example and report as an issue?
			let mut action_table = Pow::<T, Option<Action<N, T>>>::new(|x| match x {
				_ => None,
			});
			let mut reduction = Option::None;
			for item in &lalr1_span {
				match item.item.requirement() {
					Some(Symbol::Terminal(requirement)) => {
						let next_state_items = lr0::State::new(
							State::new(lalr1_span.clone())
								.step(grammar, Symbol::Terminal(requirement))
								.items
								.iter()
								.map(Item::item)
								.cloned()
								.collect(),
						)
						.summarize();
						let next_state_index = index_of_basis.get(&next_state_items.items()).ok_or(MissingState)?;

						let desired_shift_action = Action::Shift(*next_state_index);
						match action_table[requirement]
							.as_ref()
							.filter(|&action| action != &desired_shift_action)
						{
							Some(Reduce(_)) => return Err(ShiftReduce),
							Some(Shift(_)) => return Err(ShiftShift),
							None => action_table[requirement] = Some(desired_shift_action),
						}
					},
					Some(_) => (),
					None => {
						let desired_reduction = item.item.production().clone();
						match item.sentinel {
							Some(sentinel) => {
								let desired_reduction_action = Action::Reduce(desired_reduction);
								match action_table[sentinel]
									.as_ref()
									.filter(|&action| action != &desired_reduction_action)
								{
									Some(Reduce(_)) => return Err(ReduceReduce),
									Some(Shift(_)) => return Err(ShiftReduce),
									None => action_table[sentinel] = Some(desired_reduction_action),
								}
							},
							None => match reduction.as_ref().filter(|&reduction| reduction != &desired_reduction) {
								Some(_) => return Err(ReduceReduce),
								None => reduction = Some(desired_reduction),
							},
						}
					},
				}
			}
			action_tables.push(action_table);
			reductions.push(reduction);

			// Construct the GOTO table.
			let goto_table = pow![
				nonterminal => {
					let lalr1_items: BTreeSet<_> = State::new(lalr1_span.clone())
						.step(
							grammar,
							Symbol::Nonterminal(nonterminal)
						)
						.items
						.iter()
						.map(Item::item)
						.cloned()
						.collect();

					let lr0_basis = lr0::State::new(lalr1_items).summarize().items().clone();

					if lr0_basis.len() > 0 {
						index_of_basis.get(&lr0_basis).copied()
					} else {
						None
					}
				}
			];

			goto_tables.push(goto_table);
		}

		Ok(Self {
			table_by_state: lalr1_spans
				.into_iter()
				.zip(reductions.into_iter())
				.zip(action_tables.into_iter().zip(goto_tables.into_iter()))
				// NOTE: Explicit type hinting is required due to type inference bug in generic_const_exprs.
				.map(|((state, reduction), (action, goto))| Table::<N, T> {
					state,
					reduction,
					action,
					goto,
				})
				.collect(),
			initial_state: index_of_basis[&State::new(btreeset![lr1_item![0; ? -> @grammar.start(); ?]])
				.items
				.iter()
				.map(Item::item)
				.cloned()
				.collect()],
		})
	}

	// TODO: This code is really hard to read and should be cleaned up/refactored.
	// FIXME: We're using the word 'state' for two different kinds of things - the 'states'
	// of LR(0)/LR(1), and the state indices in a state machine like this.
	pub fn parse<E, L: HasTerminal<T>, X: Error>(
		&self,
		mut lexer: impl Iterator<Item = Result<L, X>>,
		mut produce: impl FnMut(&[Symbol<(N, E), L>]) -> E,
	) -> Result<E, ParseError<X>>
	where
		N: Clone + Debug,
		T: Debug,
		L: Debug,
		E: Debug,
	{
		use ParseError::*;
		let mut states = vec![self.initial_state];
		let mut expressions: Vec<Symbol<(N, E), L>> = vec![];

		while let Some(token) = lexer.next() {
			if let Ok(token) = token {
				'token: loop {
					let state = states.last().ok_or(DepletedStateStack)?;
					let table = self.table_by_state.get(*state).ok_or(InvalidState)?;
					let action = table.action[token.terminal()].as_ref().ok_or(UnexpectedTerminal)?;
					match action {
						Action::Shift(next_state) => {
							states.push(*next_state);
							expressions.push(Symbol::Terminal(token));

							break 'token;
						},
						Action::Reduce(production) => {
							let next_length = states
								.len()
								.checked_sub(production.pattern().len())
								.ok_or(OverlongReduction)?;
							states.truncate(next_length);

							let state = states.last().ok_or(DepletedStateStack)?;
							let table = self.table_by_state.get(*state).ok_or(InvalidState)?;
							let next_length = expressions
								.len()
								.checked_sub(production.pattern().len())
								.ok_or(OverlongReduction)?;

							let next_expression = produce(expressions.drain(next_length..).as_slice());
							// FIXME: This really bothers me, as if the reduction is called when encountering a terminal which is not the end symbol, then the target of the production can never be the start symbol.
							let nonterminal = production.target().ok_or(EarlyAcceptance)?;
							let next_state = table.goto[nonterminal.clone()].ok_or(UnexpectedNonterminal)?;
							states.push(next_state);
							expressions.push(Symbol::Nonterminal((nonterminal.clone(), next_expression)));
						},
					}
				}
			} else {
				token?;
			}
		}

		while let Some(state) = states.last() {
			let table = self.table_by_state.get(*state).ok_or(InvalidState)?;
			let production = table.reduction.as_ref().ok_or(UnexpectedEndOfInput)?;
			let next_length = states
				.len()
				.checked_sub(production.pattern().len())
				.ok_or(OverlongReduction)?;
			states.truncate(next_length);

			let state = states.last().ok_or(DepletedStateStack)?;
			let table = self.table_by_state.get(*state).ok_or(InvalidState)?;

			let next_length = expressions
				.len()
				.checked_sub(production.pattern().len())
				.ok_or(OverlongReduction)?;
			let next_expression = produce(expressions.drain(next_length..).as_slice());

			if let Some(nonterminal) = production.target() {
				let next_state = table.goto[nonterminal.clone()].ok_or(UnexpectedNonterminal)?;
				states.push(next_state);
				expressions.push(Symbol::Nonterminal((nonterminal.clone(), next_expression)));
			} else {
				return Ok(next_expression);
			}
		}
		Err(FailedReturn)
	}
}

mod tests {
	use enum_iterator::Sequence;

	use crate::{lalr1::*, *};

	// Figure 4.47, p. 275
	#[test]
	fn test_lalr1_kernels() {
		#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
		#[rustfmt::skip]
		enum Terminal { Id, Equals, Star, }
		use Terminal::*;

		#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
		#[repr(u8)]
		#[rustfmt::skip]
		enum Nonterminal { S, L, R, }
		use Nonterminal::*;
		impl_downset_for_repr_enum![Nonterminal ~ u8];

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

		#[rustfmt::skip]
		assert_eq!(
			lalr1::kernels(&grammar),
			btreeset![
				btreeset![
					lr1_item![0; ? -> @S; ?],
				],
				btreeset![
					lr1_item![1; ? -> @S; ?],
				],
				btreeset![
					lr1_item![1; S -> @L, !Equals, @R; ?],
					lr1_item![1; R -> @L             ; ?],
				],
				btreeset![
					lr1_item![1; S -> @R; ?],
				],
				btreeset![
					lr1_item![1; L -> !Star, @R; Equals],
					lr1_item![1; L -> !Star, @R; ?     ],
				],
				btreeset![
					lr1_item![1; L -> !Id; Equals],
					lr1_item![1; L -> !Id; ?     ],
				],
				btreeset![
					lr1_item![2; S -> @L, !Equals, @R; ?],
				],
				btreeset![
					lr1_item![2; L -> !Star, @R; Equals],
					lr1_item![2; L -> !Star, @R; ?     ],
				],
				btreeset![
					lr1_item![1; R -> @L; Equals],
					lr1_item![1; R -> @L; ?     ],
				],
				btreeset![
					lr1_item![3; S -> @L, !Equals, @R; ?]
				],
			],
		);
	}

	// The following test attempt to generate parsing tables for a grammar which is LR(1) but not LALR(1).
	#[test]
	fn test_lalr_reduce_reduce_conflict() {
		#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
		#[repr(u8)]
		#[rustfmt::skip]
		enum Terminal { U, V, X, Y, Z, }
		impl_downset_for_repr_enum![Terminal ~ u8];
		use Terminal::*;

		#[derive(Debug, Sequence, Clone, Copy, PartialOrd, Ord, Eq, PartialEq)]
		#[repr(u8)]
		#[rustfmt::skip]
		enum Nonterminal { S, A, B, }
		use Nonterminal::*;
		impl_downset_for_repr_enum![Nonterminal ~ u8];

		let grammar = grammar![
			S;
			S => [
				[!U, @A, !Y],
				[!V, @B, !Y],
				[!U, @B, !Z],
				[!V, @A, !Z],
			],
			A => [
				[!X],
			],
			B => [
				[!X]
			],
		];

		assert!(matches!(lalr1::Parser::new(&grammar), Err(GenerateParserError::ReduceReduce)));
	}
}

use std::{
	collections::{BTreeMap, BTreeSet},
	fmt::Debug,
};

use crate::{grammar::*, pow::*, slice::Slice, util::fix, *};

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
		$crate::lalr1::Item::new($crate::lr0::Item::new_at($crate::grammar::Production::new(lr1_item![@target $target], slice![$(lr1_item![@symbol $kind $symbol]),*]), $cursor), lr1_item![@target $sentinel])
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
					let successor_lr0_kernel = lr0::State::new(btreeset![lr0_item.clone()])
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

#[derive(Debug, PartialEq, Eq)]
pub enum Action<N, T> {
	Reduce(Production<N, T>),
	Shift(usize),
}

// p. 251 shows the LR parsing algorithm (how these tables are utilized!)
#[derive(Debug)]
pub struct Table<N: Downset, T: Downset>
where
	[(); Option::<T>::SIZE]:,
	[(); N::SIZE]:,
{
	state: BTreeSet<Item<N, T>>, // not necessary?
	action: Pow<Option<T>, Option<Action<N, T>>>,
	goto: Pow<N, Option<usize>>, // See p. 261, 265.
}

#[derive(Debug)]
pub struct Parser<N: Downset, T: Downset>
where
	[(); Option::<T>::SIZE]:,
	[(); N::SIZE]:,
{
	// TODO; Refer to Algorithm 4.56, p. 265
	// When constructing the parser, also keep a map from state kernels to the respective indices.
	// Or maybe keeping the list as a BTreeMap from kernels to sets is more apt for this... nah, what am I saying.
	list: Vec<Table<N, T>>,
	initial_state_index: usize,
}

impl<N: Downset, T: Downset> Parser<N, T>
where
	[(); Option::<T>::SIZE]:,
	[(); N::SIZE]:,
{
	pub fn new(grammar: &Grammar<N, T>) -> Option<Self>
	where
		N: Copy + Eq + Ord + Downset + Sequence + Debug,
		T: Copy + Eq + Ord + Sequence + Debug,
	{
		let lalr1_bases = kernels(grammar);

		let lalr1_spans: Vec<_> = lalr1_bases
			.into_iter()
			.map(|lalr1_basis| State::new(lalr1_basis).elaborate(grammar).items)
			.collect();

		// OKAY, this deviates from the algorithm, but I'm pretty sure
		// that the algorithm as described in the book
		// is actually wrongly/incompletely specified (as in this is probably
		// a necessary modification for LALR(1) as opposed to LR(1).
		//
		// The reason I believe so is that it appears to me that the
		// collection of LALR(1) states is not closed under
		// stepping by a random nonterminal and then LALR(1)-elaborating.
		// It seems to me that doing so could create states which
		// are strict subsets of other states which share the same core
		// or perhaps share the same LR(0) items entirely
		// but have different, say, lookaheads.
		//
		// TODO: Convince myself of this, or otherwise disprove it!
		let mut index_of_basis = BTreeMap::new();
		for (index, span) in lalr1_spans.clone().into_iter().enumerate() {
			// TODO: To prevent bugs, turn instances of span_to_basis into a single function on states! Maybe even LR(1) kernels, if that concept exists...
			// Yeah, that concept exists: check p. 270. 4.7.5.
			// So, convert to an LR(1) kernel, then convert to an LR(0) kernel?
			let basis: BTreeSet<_> = span.iter().map(Item::item).cloned().collect();
			index_of_basis.insert(basis, index);
		}
		let index_of_basis = index_of_basis;

		let mut action_tables = Vec::new();
		let mut goto_tables = Vec::new();
		for lalr1_span in lalr1_spans.clone() {
			// Construct the ACTION table.
			// TODO: Explicit type annotation is required due to type inference bug in generic_const_exprs.
			// TODO: Might be a good idea to construct a minimal example and report as an issue?
			let mut action_table = Pow::<Option<T>, Option<Action<N, T>>>::new(|x| match x {
				_ => None,
			});
			for item in &lalr1_span {
				match item.item.requirement() {
					Some(Symbol::Terminal(requirement)) => {
						let next_state = State::new(lalr1_span.clone()).step(grammar, Symbol::Terminal(requirement));
						let next_state_index = index_of_basis.get(&next_state.items.iter().map(Item::item).cloned().collect());

						if next_state_index.is_none() {
							println!("Could not find {:#?}", next_state.items);
							println!("Inside list {:#?}", lalr1_spans);
							println!("After stepping {:#?}", lalr1_span);
							println!("By {:#?}", requirement);
						}

						let next_state_index = next_state_index.unwrap();

						let desired_action = Some(Action::Shift(*next_state_index));
						if !action_table[Some(requirement)].is_none() && action_table[Some(requirement)] != desired_action {
							// TODO: Remove panics.
							panic!("Conflict encountered: could not resolve ambiguity in grammar.");
							return None;
						}
						action_table[Some(requirement)] = desired_action;
					},
					Some(_) => (),
					None => {
						let desired_action = Some(Action::Reduce(item.item.production().clone()));

						if !action_table[item.sentinel].is_none() && action_table[item.sentinel] != desired_action {
							// TODO: Remove panics.
							panic!("Conflict encountered: could not resolve ambiguity in grammar.");
							return None;
						}
						action_table[item.sentinel] = desired_action
					},
				}
			}
			action_tables.push(action_table);

			// Construct the GOTO table.
			let goto_table = pow![
				nonterminal =>
					index_of_basis
						.get(
							&State::new(lalr1_span.clone())
								.step(
									grammar,
									Symbol::Nonterminal(nonterminal)
								)
								.items
								.iter()
								.map(Item::item)
								.cloned()
								.collect()
						).copied()
			];
			goto_tables.push(goto_table);
		}

		Some(Self {
			list: lalr1_spans
				.into_iter()
				.zip(action_tables.into_iter().zip(goto_tables.into_iter()))
				.map(|(state, (action, goto))| Table { state, action, goto })
				.collect(),
			initial_state_index: index_of_basis[&State::new(btreeset![lr1_item![0; ? -> @grammar.start(); ?]])
				.elaborate(grammar)
				.items
				.iter()
				.map(Item::item)
				.cloned()
				.collect()],
		})
	}
}

mod tests {
	use enum_iterator::Sequence;

	use crate::*;

	// Figure 4.47, p. 275
	#[test]
	fn test_lalr1_kernels() {
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
}

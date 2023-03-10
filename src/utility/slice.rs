pub type Slice<T> = ::std::boxed::Box<[T]>;

macro_rules! slice {
	($elem:expr; $n:expr) => (
		vec![$elem; $n].into_boxed_slice()
	);
	($($x:expr),* $(,)?) => ({
		vec![$($x),*].into_boxed_slice()
	});
}
pub(crate) use slice;

// This macro provides a convenient syntax for pattern matching on an owned slice where each slice pattern takes ownership of the elements in that slice.
macro_rules! match_slice {
	[@ignore $pattern:pat] => {
	};

	{
		$slice:expr;
		$(
			[$($pattern:pat),*] => $body:expr,
		)*
		_ => $fallback_body:expr $(,)?
	} => {
		pub const fn transmute_to_slice_of_maybe_uninit<T>(
			s: ::std::boxed::Box<[T]>
		) -> ::std::boxed::Box<[::core::mem::MaybeUninit<T>]> {
			// SAFETY: MaybeUninit has the same layout as its parameter.
			unsafe { ::core::mem::transmute(s) }
		}
		#[allow(unused_variables)]
		let slice = $slice;
		// REASON: This is necessary to prevent linting for unused variables in the outer matching step, as they only get used when reintroduced in the inner step.
		#[allow(unused_variables)]
		match slice.as_ref() {
			$(
				[$($pattern),*] => {
					let _slice = transmute_to_slice_of_maybe_uninit(slice);
					#[allow(unused_variables, unused_mut)]
					let mut counter = 0;
					#[allow(unused_assignments)]
					let scrutinee =
					(
						$(
							{
								match_slice![@ignore $pattern];
								// SAFETY: This element was confirmed to exist and be initialized by the outer matching step.
								let x = unsafe {_slice.get_unchecked(counter).assume_init_read()};
								counter += 1;
								x
							},
						)*
					);
					// REASON: This is necessary to prevent linting for the unreachable pattern we introduce below.
					#[allow(unreachable_patterns)]
					match scrutinee {
						($($pattern,)*) => {
							$body
						}
						// SAFETY: This scrutinee was confirmed to match the pattern by the outer matching step.
						_ => unsafe { ::core::hint::unreachable_unchecked() }
					}
				},
			)*
			_ => {
				$fallback_body
			}
		}
	};
}

pub(crate) use match_slice;

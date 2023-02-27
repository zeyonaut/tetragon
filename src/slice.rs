pub type Slice<T> = ::std::boxed::Box<[T]>;

macro_rules! slice {
	($elem:expr; $n:expr) => (
		vec![$elem; $n].into_boxed_slice()
	);
	($($x:expr),* $(,)?) => ({
		vec![$($x),*].into_boxed_slice()
	});
}

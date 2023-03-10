pub fn apply_composed<'a, T>(mut functions: impl Iterator<Item = &'a dyn Fn(T) -> T>, x: T) -> T
where
	T: 'a,
{
	if let Some(function) = functions.next() {
		apply_composed(functions, function(x))
	} else {
		x
	}
}

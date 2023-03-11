pub fn apply_composed<T>(mut functions: impl Iterator<Item = Box<dyn FnOnce(T) -> T>>, x: T) -> T {
	if let Some(function) = functions.next() {
		apply_composed(functions, function(x))
	} else {
		x
	}
}

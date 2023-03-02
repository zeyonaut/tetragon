pub fn fix<T>(point: &T, mut map: impl FnMut(&T) -> T) -> T
where
	T: Eq + Clone,
{
	let mut point = point.clone();
	loop {
		let new_point = map(&point);
		if new_point == point {
			break new_point;
		} else {
			point = new_point;
		}
	}
}

pub fn fix<T>(mut point: T, mut map: impl FnMut(&T) -> T) -> T
where
	T: Eq,
{
	loop {
		let new_point = map(&point);
		if new_point == point {
			break new_point;
		} else {
			point = new_point;
		}
	}
}

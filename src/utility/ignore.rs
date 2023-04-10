pub trait Ignore {
	fn ignore(self)
	where
		Self: Sized,
	{
	}
}

impl<const N: usize> Ignore for [(); N] {}

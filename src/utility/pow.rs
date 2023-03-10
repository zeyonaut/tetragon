use core::{
	iter::{Map, Zip},
	mem::MaybeUninit,
	ops::{Index, IndexMut, Range},
};

// A downset is isomorphic to an initial segment of usize.
pub trait Downset {
	const SIZE: usize;
	fn into_usize(self) -> usize;
	fn from_usize(index: usize) -> Self;
}

// This may be used to implement Downset for enums which are represented by a subtype of usize.
macro_rules! impl_downset_for_repr_enum {
	[$enum:ident ~ $repr:ident] => {
		impl $crate::utility::pow::Downset for $enum {
			const SIZE: usize = ::core::mem::variant_count::<Self>();
			fn from_usize(index: usize) -> Self {
				// SAFETY: The caller must ensure that any number in 0..Self::SIZE is a valid $enum.
				unsafe {
					::core::mem::transmute::<$repr, Self>(::core::cmp::min(index, Self::SIZE - 1) as $repr)
				}
			}
			fn into_usize(self) -> usize {
				usize::from(self as $repr)
			}
		}
	};
}
pub(crate) use impl_downset_for_repr_enum;

impl<D: Downset> Downset for Option<D> {
	const SIZE: usize = D::SIZE + 1;
	fn from_usize(index: usize) -> Self {
		if index >= D::SIZE {
			None
		} else {
			Some(D::from_usize(index))
		}
	}
	fn into_usize(self) -> usize {
		match self {
			None => D::SIZE,
			Some(d) => d.into_usize(),
		}
	}
}

// This returns an iterator over all points in a downset.
pub fn points<D: Downset>() -> Map<Range<usize>, fn(usize) -> D> {
	(0..D::SIZE).map(D::from_usize)
}

// A pow is a map out of a downset.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pow<D: Downset, T>
// FIXME: This const generic bound is forward-incompatible syntax.
where
	[(); D::SIZE]:,
{
	items: [T; D::SIZE],
}

impl<D: Downset, T> Pow<D, T>
where
	[(); D::SIZE]:,
{
	pub fn new(map: impl Fn(D) -> T) -> Self
	where
		D: Clone,
	{
		let mut items = MaybeUninit::<[T; D::SIZE]>::uninit().transpose();
		for i in points::<D>() {
			let index = i.clone().into_usize();
			// SAFETY: index must be in the range 0..D::SIZE. This is guaranteed by the definition of D::points.
			unsafe { items.get_unchecked_mut(index) }.write(map(i));
		}
		let items = items.transpose();
		// SAFETY: The image of the range of D::points under D::into_usize must be 0..D::SIZE. This is promised by implementers of Downset, of which D is one.
		let items = unsafe { items.assume_init() };
		Self { items }
	}

	pub fn iter(&self) -> Zip<Map<Range<usize>, fn(usize) -> D>, core::slice::Iter<T>> {
		core::iter::zip(points::<D>(), self.items.iter())
	}
}

macro_rules! pow {
	[$($token_trees:tt)*] => {
		$crate::utility::pow::Pow::new(|_76e5cca5354f477f9fc05eaafc5c071e| match _76e5cca5354f477f9fc05eaafc5c071e {
			$($token_trees)*
		})
	};
}
pub(crate) use pow;

impl<D: Downset, T> Index<D> for Pow<D, T>
where
	[(); D::SIZE]:,
{
	type Output = T;

	fn index(&self, index: D) -> &Self::Output {
		// SAFETY: D::into_usize must have a range of 0..D::SIZE
		unsafe { self.items.get_unchecked(index.into_usize()) }
	}
}

impl<D: Downset, T> IndexMut<D> for Pow<D, T>
where
	[(); D::SIZE]:,
{
	fn index_mut(&mut self, index: D) -> &mut Self::Output {
		// SAFETY: D::into_usize must have a range of 0..D::SIZE
		unsafe { self.items.get_unchecked_mut(index.into_usize()) }
	}
}

#[derive(Clone, Debug)]
pub struct LabelGenerator(u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Label(u64);

impl Label {
	pub fn handle(&self) -> u64 {
		self.0
	}
}

impl LabelGenerator {
	pub fn new() -> Self {
		Self(0)
	}

	pub fn fresh<const N: usize>(&mut self) -> [Label; N] {
		[(); N].map(|()| {
			let symbol = self.0;
			self.0 += 1;
			Label(symbol)
		})
	}
}

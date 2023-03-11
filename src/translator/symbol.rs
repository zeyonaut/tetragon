pub struct SymbolGenerator(u64);

impl SymbolGenerator {
	pub fn new() -> Self {
		Self(0)
	}

	pub fn fresh(&mut self) -> u64 {
		let symbol = self.0;
		self.0 += 1;
		symbol
	}
}

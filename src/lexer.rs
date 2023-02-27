use std::{iter::Peekable, str::Chars};

// TODO: Create a second enum with the same variants
// without the fields.
// See https://users.rust-lang.org/t/how-to-parse-enum-macro/36161
// The fieldless enum will act as a set of terminals for the parser generator.
#[derive(Debug)]
pub enum Token {
	Arrova,
	Bar,
	Bicolon,
	CloseAngle,
	CloseParen,
	Equals,
	Exclaim,
	Integer(i64),
	Name(String),
	OpenAngle,
	OpenParen,
	Question,
	Semicolon,
}

pub struct Lexer<'source> {
	chars: Peekable<Chars<'source>>,
}

impl<'source> Lexer<'source> {
	pub fn new(source: &'source str) -> Self {
		Self {
			chars: source.chars().peekable(),
		}
	}
}

impl<'source> Iterator for Lexer<'source> {
	type Item = Token;

	fn next(&mut self) -> Option<Self::Item> {
		use Token::*;
		while self.chars.next_if(|&x| x.is_ascii_whitespace()).is_some() {}
		Some(match self.chars.next()? {
			'@' => Arrova,
			'|' => Bar,
			':' => {
				if self.chars.next_if(|&x| x == ':').is_some() {
					Bicolon
				} else {
					None?
				}
			},
			'>' => CloseAngle,
			')' => CloseParen,
			'=' => Equals,
			'!' => Exclaim,
			'<' => OpenAngle,
			'(' => OpenParen,
			'?' => Question,
			';' => Semicolon,
			x if x.is_ascii_alphabetic() => {
				let mut name = String::new();
				name.push(x);
				while let Some(y) = self.chars.next_if(|&y| y.is_ascii_alphanumeric() || y == '-') {
					name.push(y);
				}
				Name(name)
			},
			x if x.is_ascii_digit() || x == '+' || x == '-' => {
				let mut integer = String::new();
				integer.push(x);
				while let Some(y) = self.chars.next_if(|&y| y.is_ascii_alphanumeric() || y == '-') {
					integer.push(y);
				}
				Integer(integer.parse::<i64>().ok()?)
			},
			_ => None?,
		})
	}
}

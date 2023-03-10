use std::{iter::Peekable, str::Chars};

use enum_iterator::Sequence;
use thiserror::Error;

use crate::{generator::terminal::*, util::pow::impl_downset_for_repr_enum};

create_token_and_terminal_types! {
	#[derive(Debug)]
	pub enum Token {
		Arrova,
		Arrow,
		Asterisk,
		Bar,
		Bicolon,
		CloseCurly,
		CloseOrtho,
		CloseParen,
		Comma,
		EqualsQuestion,
		IntegerLiteral(i64),
		Name(String),
		OpenCurly,
		OpenOrtho,
		OpenParen,
		Period,
		Question,
	}

	#[derive(Debug, Clone, Copy, Eq, Ord, PartialEq, PartialOrd, Sequence)]
	pub enum Terminal ~ u8;
}

impl_downset_for_repr_enum![Terminal ~ u8];

struct Scanner<'source> {
	chars: Peekable<Chars<'source>>,
	line: usize,
	offset: usize,
}

impl<'source> Scanner<'source> {
	// NOTE: I have no idea if this line/offset numbering convention is standard.
	fn new(chars: Peekable<Chars<'source>>) -> Self {
		Self {
			chars,
			line: 1,
			offset: 0,
		}
	}

	fn increment_counters(&mut self, x: char) {
		if x == '\n' {
			self.line += 1;
			self.offset = 0;
		} else {
			self.offset += 1;
		}
	}

	fn next(&mut self) -> Option<char> {
		self.chars.next().map(|x| {
			self.increment_counters(x);
			x
		})
	}

	fn next_if(&mut self, func: impl FnOnce(&char) -> bool) -> Option<char> {
		self.chars.next_if(func).map(|x| {
			self.increment_counters(x);
			x
		})
	}

	fn next_if_eq(&mut self, c: &char) -> Option<char> {
		self.chars.next_if_eq(c).map(|x| {
			self.increment_counters(x);
			x
		})
	}

	fn skip_whitespace(&mut self) {
		while self.next_if(|&x| x.is_ascii_whitespace()).is_some() {}
	}
}

#[derive(Error, Debug)]
pub enum LexError {
	#[error(transparent)]
	ParseIntError(#[from] core::num::ParseIntError),
	#[error("encountered unknown lexeme '{}' at {}:{}", .lexeme, .line, .offset)]
	UnknownLexeme { lexeme: String, line: usize, offset: usize },
}

/// Takes a first character and a peekable stream of characters and produces a token representing a name.
fn lex_name(head: char, tail: &mut Scanner) -> Token {
	use Token::Name;
	let mut name = String::from(head);
	while let Some(y) = tail.next_if(|&y| y.is_ascii_alphanumeric() || y == '-') {
		name.push(y);
	}
	Name(name)
}

/// Takes a first character and a peekable stream of characters and may produce a token representing an integer.
fn lex_integer(head: char, tail: &mut Scanner) -> Result<Token, LexError> {
	use Token::IntegerLiteral;
	let mut integer = String::from(head);
	while let Some(y) = tail.next_if(|&y| y.is_ascii_digit()) {
		integer.push(y);
	}
	Ok(IntegerLiteral(integer.parse::<i64>()?))
}

pub struct Lexer<'source> {
	scanner: Scanner<'source>,
}

impl<'source> Lexer<'source> {
	pub fn new(source: &'source str) -> Self {
		Self {
			scanner: Scanner::new(source.chars().peekable()),
		}
	}

	pub fn line(&self) -> usize {
		self.scanner.line
	}

	pub fn offset(&self) -> usize {
		self.scanner.offset
	}
}

impl<'source> Iterator for Lexer<'source> {
	type Item = Result<Token, LexError>;

	fn next(&mut self) -> Option<Self::Item> {
		use LexError::*;
		use Token::*;
		while self.scanner.next_if(|&x| x.is_ascii_whitespace()).is_some() {}
		Some(match self.scanner.next()? {
			'@' => Ok(Arrova),
			'-' => self
				.scanner
				.next_if_eq(&'>')
				.map(|_| Ok(Arrow))
				.unwrap_or_else(|| lex_integer('-', &mut self.scanner)),
			'*' => Ok(Asterisk),
			'|' => Ok(Bar),
			':' => self.scanner.next_if_eq(&':').map(|_| Ok(Bicolon)).unwrap_or_else(|| {
				Err(UnknownLexeme {
					lexeme: ":".to_owned(),
					line: self.line(),
					offset: self.offset(),
				})
			}),
			'}' => Ok(CloseCurly),
			']' => Ok(CloseOrtho),
			')' => Ok(CloseParen),
			',' => Ok(Comma),
			'=' => self.scanner.next_if_eq(&'?').map(|_| Ok(EqualsQuestion)).unwrap_or_else(|| {
				Err(UnknownLexeme {
					lexeme: "=".to_owned(),
					line: self.line(),
					offset: self.offset(),
				})
			}),
			'{' => Ok(OpenCurly),
			'[' => Ok(OpenOrtho),
			'(' => Ok(OpenParen),
			'.' => Ok(Period),
			'?' => Ok(Question),
			x if x.is_ascii_alphabetic() => Ok(lex_name(x, &mut self.scanner)),
			x if x.is_ascii_digit() || x == '+' => lex_integer(x, &mut self.scanner),
			x => Err(UnknownLexeme {
				lexeme: String::from(x),
				line: self.line(),
				offset: self.offset(),
			}),
		})
	}
}

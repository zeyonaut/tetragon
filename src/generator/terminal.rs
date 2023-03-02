// Indicates that a type is trivially discriminated by a terminal.
pub trait HasTerminal<T> {
	fn terminal(&self) -> T;
}

// Create a enum of tokens and an enum of terminals, where the token type
// implements HasTerminal for the terminal type.
macro_rules! create_token_and_terminal_types {
	// Auxilliary: Converts a type to an underscore pattern for pattern matching.
	[@convert_type_to_underscore $Type:ty] => {
		_
	};

	// Auxilliary: Creates a pattern for pattern matching.
	[@terminal_match_line $TokenTypeName:ident $VariantName:ident ($($Type:ty),*)] => {
		$TokenTypeName::$VariantName($(create_token_and_terminal_types![@convert_type_to_underscore $Type]),*)
	};

	// Auxilliary: Creates a pattern for pattern matching.
	[@terminal_match_line $TokenTypeName:ident $VariantName:ident] => {
		$TokenTypeName::$VariantName
	};

	// Entry: Create two enumerated types, with a HasTerminal implementation connecting the two.
	{
		$(#[$attr_token:meta])*
		$pub_token:vis enum $TokenTypeName:ident {
			$(
				$VariantName:ident
				$(
					( $($Type:ty),* )
				)?
			),*
			$(,)?
		}
		$(#[$attr_terminal:meta])*
		$pub_terminal:vis enum $TerminalTypeName:ident ~ $repr:ident;
	} => {
		$(#[$attr_token])*
		$pub_token enum $TokenTypeName {
			$($VariantName $(($($Type),*))?),*
		}

		$(#[$attr_terminal])*
		#[repr($repr)]
		$pub_terminal enum $TerminalTypeName {
			$($VariantName),*
		}

		impl HasTerminal<$TerminalTypeName> for $TokenTypeName {
			fn terminal(&self) -> $TerminalTypeName {
				match self {
					$(
						create_token_and_terminal_types![@terminal_match_line $TokenTypeName $VariantName $(($($Type),*))?] => $TerminalTypeName::$VariantName
					),*
				}
			}
		}
	};
}
pub(crate) use create_token_and_terminal_types;

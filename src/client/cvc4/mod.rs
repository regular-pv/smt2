use std::convert::TryFrom;
use std::fmt;

#[derive(Clone, PartialEq)]
pub struct Constant {
	sort: String,
	index: u32,
}

impl super::Constant for Constant {
	fn sort_id(&self) -> &String {
		&self.sort
	}

	fn index(&self) -> u32 {
		self.index
	}
}

pub struct NotCVC4Constant;

impl TryFrom<String> for Constant {
	type Error = NotCVC4Constant;

	fn try_from(str: String) -> Result<Self, Self::Error> {
		if str.len() > 7 {
			if &str[0..4] == "@uc_" {
				let chars = str.chars().skip(4);
				let mut sort = String::new();
				let mut in_index = false;
				let mut index = 0;

				for c in chars {
					if in_index {
						if let Some(d) = c.to_digit(10) {
							index = index * 10 + d;
						} else {
							return Err(NotCVC4Constant);
						}
					} else {
						if c == '_' {
							in_index = true;
						} else {
							sort.push(c)
						}
					}
				}

				if !sort.is_empty() {
					return Ok(Constant {
						sort: sort,
						index: index,
					});
				}
			}
		}

		Err(NotCVC4Constant)
	}
}

impl fmt::Display for Constant {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "@uc_{}_{}", self.sort, self.index)
	}
}

use source_span::Span;
use std::fmt;
use std::ops::Deref;

/**
 * Wrap a value to give it a location.
 */
pub struct Located<T> {
	t: T,
	span: Span
}

impl<T> Located<T> {
	pub fn new(t: T, span: Span) -> Located<T> {
		Located {
			t: t,
			span: span
		}
	}

	pub fn into_inner(self) -> T {
		self.t
	}

	pub fn span(&self) -> Span {
		self.span
	}
}

impl<T> Deref for Located<T> {
	type Target = T;

	fn deref(&self) -> &T {
		&self.t
	}
}

impl<T: PartialEq> PartialEq for Located<T> {
	fn eq(&self, other: &Located<T>) -> bool {
		self.span == other.span && self.t == other.t
	}
}

impl<T: Eq> Eq for Located<T> {}

impl<T: fmt::Display> fmt::Display for Located<T> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.t.fmt(f)
    }
}

impl<T: fmt::Debug> fmt::Debug for Located<T> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self.t.fmt(f)
    }
}

impl<T: Clone> Clone for Located<T> {
	fn clone(&self) -> Self {
		Located {
			t: self.t.clone(),
			span: self.span
		}
	}
}

impl<T> AsRef<T> for Located<T> {
	fn as_ref(&self) -> &T {
		&self.t
	}
}

impl<T> AsMut<T> for Located<T> {
	fn as_mut(&mut self) -> &mut T {
		&mut self.t
	}
}

use std::fmt;
use std::cmp::{Ordering, Ord, PartialOrd};
use std::hash::{Hash, Hasher};

pub trait SortedWith<S> {
    fn sort(&self) -> &S;
}

pub struct Sorted<X, T>(pub X, pub T);

impl<X, T> Sorted<X, T> {
    pub fn new(x: X, t: T) -> Sorted<X, T> {
        Sorted(x, t)
    }
}

impl<X, T> SortedWith<T> for Sorted<X, T> {
    fn sort(&self) -> &T {
        &self.1
    }
}

impl<X: Ord, T: Ord> Ord for Sorted<X, T> {
    fn cmp(&self, other: &Sorted<X, T>) -> Ordering {
        match self.1.cmp(&other.1) {
            Ordering::Equal => self.0.cmp(&other.0),
            ord => ord
        }
    }
}

impl<X: PartialOrd, T: PartialOrd> PartialOrd for Sorted<X, T> {
    fn partial_cmp(&self, other: &Sorted<X, T>) -> Option<Ordering> {
        match self.1.partial_cmp(&other.1) {
            Some(Ordering::Equal) => self.0.partial_cmp(&other.0),
            Some(ord) => Some(ord),
            None => None
        }
    }
}

impl<X: Eq, T: Eq> Eq for Sorted<X, T> {}

impl<X:PartialEq, T: PartialEq> PartialEq for Sorted<X, T> {
    fn eq(&self, other: &Sorted<X, T>) -> bool {
        self.1 == other.1 && self.0 == other.0
    }
}

impl<X: Hash, T: Hash> Hash for Sorted<X, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
        self.1.hash(state);
    }
}

impl<X: Copy, T: Copy> Copy for Sorted<X, T> {}

impl<X: Clone, T: Clone> Clone for Sorted<X, T> {
    fn clone(&self) -> Sorted<X, T> {
        Sorted(self.0.clone(), self.1.clone())
    }
}

impl<X: fmt::Display, T: fmt::Display> fmt::Display for Sorted<X, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:{}", self.0, self.1)
    }
}

impl<X: fmt::Debug, T: fmt::Debug> fmt::Debug for Sorted<X, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}:{:?}", self.0, self.1)
    }
}

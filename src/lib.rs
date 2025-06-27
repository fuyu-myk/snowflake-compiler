#[macro_export]
macro_rules! idx {
    ($name:ident) => {
        #[derive(Debug, Clone, Eq, PartialEq, Hash, Copy)]
        pub struct $name {
            pub index: usize,
        }

        impl Idx for $name {
            fn as_index(&self) -> usize {
                return self.index;
            }

            fn new(index: usize) -> Self {
                Self { index }
            }
        }
    };
}

#[macro_export]
macro_rules! bug_report {
    ($( $arg:tt )*) => {
        panic!("There seems to be a bug with the compiler.\n {}", format_args!($($arg)*))
    };
}

pub trait Idx: Copy + Clone + Sized {
    fn as_index(&self) -> usize;

    fn new(index: usize) -> Self;

    fn unreachable() -> Self {
        Self::new(usize::MAX)
    }

    fn first() -> Self {
        Self::new(0)
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct IndexVec<Index, T> where Index: Idx {
    vec: Vec<T>,
    _marker: std::marker::PhantomData<Index>,
}

impl<Index, T> IndexVec<Index, T> where Index: Idx {
    pub fn new() -> Self {
        Self { vec: vec![], _marker: std::marker::PhantomData }
    }

    pub fn push(&mut self, value: T) -> Index {
        let next_index = self.vec.len();
        self.vec.push(value);

        return Index::new(next_index);
    }

    pub fn push_with_index(&mut self, value: impl FnOnce(Index) -> T) -> Index {
        let next_index = Index::new(self.vec.len());
        self.vec.push(value(next_index));

        next_index
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.vec.iter()
    }

    pub fn indexed_iter(&self) -> impl Iterator<Item = (Index, &T)> {
        self.vec.iter().enumerate().map(|(index, value)| (Index::new(index), value))
    }

    pub fn cloned_indices(&self) -> Vec<Index> {
        self.vec.iter().enumerate().map(|(index, _)| Index::new(index)).collect()
    }

    pub fn get(&self, index: Index) -> &T {
        return &self[index];
    }

    pub fn get_mut(&mut self, index: Index) -> &mut T {
        &mut self[index]
    }
}

impl<Index: Idx, T> std::ops::Index<Index> for IndexVec<Index, T> {
    type Output = T;

    fn index(&self, index: Index) -> &T {
        return &self.vec[index.as_index()];
    }
}

impl<Index: Idx, T> std::ops::IndexMut<Index> for IndexVec<Index, T> {
    fn index_mut(&mut self, index: Index) -> &mut T {
        return &mut self.vec[index.as_index()]
    }
}

impl<I: Idx, T> IndexVec<I, Option<T>> {
    #[inline]
    pub fn get_or_panic(&self, index: I) -> &T {
        self.get(index).as_ref().unwrap_or_else(|| crate::bug_report!("Index {} does not exist", index.as_index()))
    }

    #[inline]
    pub fn get_mut_or_panic(&mut self, index: I) -> &mut T {
        self.get_mut(index).as_mut().unwrap_or_else(|| crate::bug_report!("Index {} does not exist", index.as_index()))
    }

    #[inline]
    pub fn indexed_iter_as_option(&self) -> impl Iterator<Item = Option<(I, &T)>> {
        self.vec.iter().enumerate()
            .map(|(index, value)| value.as_ref()
            .map(|value| (I::new(index), value)))
    }

    #[inline]
    pub fn remove(&mut self, index: I) -> Option<T> {
        self.vec[index.as_index()].take()
    }
}
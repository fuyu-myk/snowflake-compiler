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
        panic!("There seems to be a bug with the compiler.\n {}", format_args!($($arg)*));
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

impl <Index, T> IndexVec<Index, T> where Index: Idx {
    pub fn new() -> Self {
        Self { vec: vec![], _marker: std::marker::PhantomData }
    }

    pub fn push(&mut self, value: T) -> Index {
        let next_index = self.vec.len();
        self.vec.push(value);

        return Index::new(next_index);
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
}

impl <Index, T> std::ops::Index<Index> for IndexVec<Index, T> where Index: Idx {
    type Output = T;

    fn index(&self, index: Index) -> &T {
        return &self.vec[index.as_index()];
    }
}

impl <Index, T> std::ops::IndexMut<Index> for IndexVec<Index, T> where Index: Idx {
    fn index_mut(&mut self, index: Index) -> &mut T {
        return &mut self.vec[index.as_index()]
    }
}
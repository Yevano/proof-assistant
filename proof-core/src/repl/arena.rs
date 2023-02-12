pub struct Arena<T> {
    arena: Vec<T>,
}

#[derive(Debug)]
pub struct ArenaRef<T> {
    _marker: std::marker::PhantomData<T>,
    index: usize,
}

impl<T> Clone for ArenaRef<T> {
    fn clone(&self) -> Self {
        ArenaRef { _marker: Default::default(), index: self.index }
    }
}

impl<T> Copy for ArenaRef<T> {}

impl<T> Arena<T> {
    pub fn new() -> Self {
        Self { arena: Vec::new() }
    }

    pub fn alloc(&mut self, value: T) -> ArenaRef<T> {
        let index = self.arena.len();
        self.arena.push(value);
        ArenaRef { _marker: Default::default(), index }
    }

    pub fn get(&self, index: ArenaRef<T>) -> &T {
        &self.arena[index.index]
    }

    pub fn get_mut(&mut self, index: ArenaRef<T>) -> &mut T {
        &mut self.arena[index.index]
    }
}

// Iter for Arena
impl<T> IntoIterator for Arena<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.arena.into_iter()
    }
}
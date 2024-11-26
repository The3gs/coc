use std::{
    collections::BTreeMap,
    sync::{Arc, RwLock},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Token(u32);

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(s) = self.get_arc() {
            write!(f, "Token({} {:?})", self.0, s)
        } else {
            write!(f, "Token({})", self.0)
        }
    }
}

impl Token {
    pub fn get_arc(&self) -> Option<Arc<str>> {
        STRINGS
            .read()
            .expect("Should not be poisoned")
            .1
            .get(self.0 as usize)
            .expect("Should always have string for token")
            .clone()
    }
}

static STRINGS: RwLock<(BTreeMap<Arc<str>, Token>, Vec<Option<Arc<str>>>)> =
    RwLock::new((BTreeMap::new(), Vec::new()));

/// intern a string, returning a token which can be used consistently in it's place.
pub fn intern(s: &str) -> Token {
    let lock = STRINGS
        .read()
        .expect("Poisened RwLock on strings interning mechanism");
    if let Some(token) = lock.0.get(s) {
        *token
    } else {
        drop(lock);
        let mut lock = STRINGS
            .write()
            .expect("Poisoned RWLock on strings interning mechanism");
        // We need to check again once we get the write lock to ensure no other accessors were attempting to add this string as well.
        if let Some(token) = lock.0.get(s) {
            *token
        } else {
            let token = Token(lock.1.len() as u32);
            let arc: Arc<str> = Arc::from(s);
            lock.0.insert(arc.clone(), token);
            lock.1.push(Some(arc));
            token
        }
    }
}

/// Creates a unique token, guaranted to be different from all tokens not copied from the original.
pub fn unique() -> Token {
    let mut lock = STRINGS.write().unwrap();
    let token = Token(lock.1.len() as u32);
    lock.1.push(None);
    token
}

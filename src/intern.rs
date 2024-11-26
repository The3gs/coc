use std::{
    collections::BTreeMap,
    sync::{atomic::AtomicU32, Arc, RwLock},
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Token(u32);

impl std::fmt::Debug for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Token({} {:?})",
            self.0,
            STRINGS
                .read()
                .expect("Should not be poisoned")
                .1
                .get(self.0 as usize)
                .unwrap()
                .as_ref()
        )
    }
}

impl Token {
    pub fn get_arc(&self) -> Arc<str> {
        STRINGS
            .read()
            .expect("Should not be poisoned")
            .1
            .get(self.0 as usize)
            .expect("Should always have string for token")
            .clone()
    }
}

static STRINGS: RwLock<(BTreeMap<Arc<str>, Token>, Vec<Arc<str>>)> =
    RwLock::new((BTreeMap::new(), Vec::new()));

static NEXT_TOKEN: AtomicU32 = AtomicU32::new(0);

pub fn intern(s: &str) -> (Token, Arc<str>) {
    let lock = STRINGS
        .read()
        .expect("Poisened RwLock on strings interning mechanism");
    if let Some(token) = lock.0.get(s) {
        (*token, lock.1.get(token.0 as usize).unwrap().clone())
    } else {
        drop(lock);
        let mut lock = STRINGS
            .write()
            .expect("Poisoned RWLock on strings interning mechanism");
        // We need to check again once we get the write lock to ensure no other accessors were attempting to add this string as well.
        if let Some(token) = lock.0.get(s) {
            (*token, lock.1.get(token.0 as usize).unwrap().clone())
        } else {
            let token = Token(NEXT_TOKEN.fetch_add(1, std::sync::atomic::Ordering::Relaxed));
            let arc: Arc<str> = Arc::from(s);
            lock.0.insert(arc.clone(), token);
            lock.1.push(arc.clone());
            (token, arc)
        }
    }
}

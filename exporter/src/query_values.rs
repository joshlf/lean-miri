//! Typed compiler query catalogs and their local reference finalization.
use serde::Serialize;
#[derive(Clone, Serialize)]
pub(super) struct PredicateQuery {
    pub predicate_id: usize,
    pub typing_env: &'static str,
    pub auto_trait: bool,
    pub original: u64,
    pub normalization: u64,
    pub erased: u64,
    pub stable_key: u64,
}

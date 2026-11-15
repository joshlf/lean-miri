// Generic source templates: no enumeration of type/const instantiations.
pub fn identity<T: Copy>(value: T) -> T { value }
pub fn array_identity<T: Copy, const N: usize>(value: [T; N]) -> [T; N] { value }
pub fn concrete(value: [u16; 3]) -> [u16; 3] { value }
// Deliberately outside the initial foundation subset: the exporter must fail.
pub fn calls(value: u8) -> u8 { identity(value) }

pub struct Link<T> {
    pub value: T,
    pub next: *const Link<T>,
}
pub fn link_identity(value: Link<u8>) -> Link<u8> { value }

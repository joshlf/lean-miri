pub fn identity(value: fn() -> ()) -> fn() -> () { value }
pub fn raw_identity(value: *const u8) -> *const u8 { value }

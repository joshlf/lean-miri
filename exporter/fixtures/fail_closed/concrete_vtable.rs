#![no_std]

trait Base {
    fn value(&self) -> u32;
}

trait Side {
    fn side(&self) -> u32;
}

trait Both: Base + Side {}

struct Item;

impl Base for Item {
    fn value(&self) -> u32 { 1 }
}

impl Side for Item {
    fn side(&self) -> u32 { 2 }
}

impl Both for Item {}

pub fn root() -> u32 {
    let value = Item;
    let object: &dyn Both = &value;
    object.value()
}

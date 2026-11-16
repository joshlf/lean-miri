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

static ITEM: Item = Item;
const OBJECT: &(dyn Both + Sync) = &ITEM;
const CALLBACK: fn(u32) -> u32 = identity::<u32>;

fn identity<T>(value: T) -> T { value }

fn main() {
    let value = Item;
    let both: &(dyn Both + Send) = &value;
    let erased: &dyn Both = both;
    let side: &dyn Side = erased;
    assert_eq!(side.side(), 2);
    assert_eq!(both.value(), 1);
    let constant: &dyn Both = OBJECT;
    assert_eq!(constant.value(), 1);
    assert_eq!(CALLBACK(5), 5);
}

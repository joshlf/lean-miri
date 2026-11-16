#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_hashes;
extern crate rustc_index;
use rustc_abi::{
    Align, BackendRepr, FieldsShape, Integer, LayoutCalculator, LayoutData, Primitive, ReprFlags,
    ReprOptions, Scalar, Size, StructKind, TargetDataLayout, Variants, WrappingRange,
};
use rustc_hashes::Hash64;
use rustc_index::IndexVec;
type L = LayoutData<usize, usize>;
fn field(dl: &TargetDataLayout, code: u8) -> L {
    let (i, start, end) = match code {
        0 => (Integer::I8, 0, 255),
        1 => (Integer::I8, 0, 1),
        2 => (Integer::I16, 0, 65535),
        3 => (Integer::I32, 0, u32::MAX as u128),
        4 => (Integer::I32, 1, u32::MAX as u128),
        5 => (Integer::I64, 0, u64::MAX as u128),
        6 => return L::unit(dl, true),
        7 => {
            return LayoutCalculator::new(dl)
                .layout_of_array_like::<usize, usize, &&L>(&field(dl, 0), None)
                .unwrap()
        }
        _ => unreachable!(),
    };
    L::scalar(
        dl,
        Scalar::Initialized {
            value: Primitive::Int(i, false),
            valid_range: WrappingRange { start, end },
        },
    )
}
fn main() {
    let mut dl = TargetDataLayout::default();
    dl.i64_align = Align::from_bytes(8).unwrap();
    dl.i128_align = Align::from_bytes(16).unwrap();
    let patterns: &[&[u8]] = &[
        &[0, 1, 3, 1, 5, 2],
        &[5, 0, 4, 3, 0],
        &[6, 3, 1, 6, 5, 1],
        &[0, 1, 3, 1, 5, 7],
    ];
    for seed in [0, 1, 42, u64::MAX] {
        for (pattern, codes) in patterns.iter().enumerate() {
            for mode in 0..3 {
                if pattern == 3 && mode != 1 {
                    continue;
                }
                for pack in [0, 2] {
                    for requested in [0, 16] {
                        let values: Vec<L> = codes.iter().map(|code| field(&dl, *code)).collect();
                        let refs: Vec<&L> = values.iter().collect();
                        let fields: IndexVec<usize, &&L> = refs.iter().collect();
                        let repr = ReprOptions {
                            flags: ReprFlags::RANDOMIZE_LAYOUT,
                            field_shuffle_seed: Hash64::new(seed),
                            pack: (pack != 0).then(|| Align::from_bytes(pack).unwrap()),
                            align: (requested != 0).then(|| Align::from_bytes(requested).unwrap()),
                            ..ReprOptions::default()
                        };
                        let kind = match mode {
                            0 => StructKind::AlwaysSized,
                            1 => StructKind::MaybeUnsized,
                            _ => StructKind::Prefixed(
                                Size::from_bytes(4),
                                Align::from_bytes(8).unwrap(),
                            ),
                        };
                        let layout = LayoutCalculator::new(&dl)
                            .layout_of_univariant(&fields, &repr, kind)
                            .unwrap();
                        assert!(!layout.repr_c && !layout.uninhabited);
                        assert!(matches!(layout.variants, Variants::Single { index: 0 }));
                        let BackendRepr::Memory { sized } = layout.backend_repr else {
                            panic!("unexpected scalar ABI");
                        };
                        let FieldsShape::Arbitrary {
                            offsets,
                            in_memory_order,
                        } = layout.fields
                        else {
                            panic!()
                        };
                        let niche = layout
                            .largest_niche
                            .map(|n| {
                                format!(
                                    "{},{},{},{}",
                                    n.offset.bytes(),
                                    n.value.size(&dl).bytes(),
                                    n.valid_range.start,
                                    n.valid_range.end
                                )
                            })
                            .unwrap_or_else(|| "none".to_owned());
                        println!("a {seed} {pattern} {mode} {pack} {requested} {} {} {} {} {} {sized} {:?} {:?} {niche}",layout.size.bytes(),layout.align.abi.bytes(),layout.unadjusted_abi_align.bytes(),layout.max_repr_align.map(|a|a.bytes()).unwrap_or(0),layout.randomization_seed.as_u64(),offsets.iter().map(|s|s.bytes()).collect::<Vec<_>>(),in_memory_order.raw);
                    }
                }
            }
        }
    }
}

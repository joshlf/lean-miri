#![feature(rustc_private)]
extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_index;
use rustc_abi::{
    FieldsShape, Integer, LayoutCalculator, LayoutData, Primitive, Scalar, TargetDataLayout,
    Variants, WrappingRange,
};
use rustc_index::{bit_set::BitMatrix, IndexVec};
type L = LayoutData<usize, usize>;
fn scalar(dl: &TargetDataLayout, i: Integer) -> L {
    L::scalar(
        dl,
        Scalar::Initialized {
            value: Primitive::Int(i, false),
            valid_range: WrappingRange::full(i.size()),
        },
    )
}
fn main() {
    let mut dl = TargetDataLayout::default();
    dl.i64_align = rustc_abi::Align::from_bytes(8).unwrap();
    dl.i128_align = rustc_abi::Align::from_bytes(16).unwrap();
    let cases = vec![
        (vec![], vec![], vec![vec![], vec![], vec![]], vec![]),
        (
            vec![Integer::I32, Integer::I64],
            vec![],
            vec![vec![], vec![0], vec![1]],
            vec![vec![], vec![]],
        ),
        (
            vec![Integer::I32, Integer::I64],
            vec![],
            vec![vec![], vec![0], vec![1]],
            vec![vec![1], vec![0]],
        ),
        (
            vec![Integer::I8, Integer::I32, Integer::I64],
            vec![],
            vec![vec![], vec![0, 1], vec![1, 2]],
            vec![vec![], vec![], vec![]],
        ),
        (
            vec![Integer::I128, Integer::I32, Integer::I64],
            vec![Integer::I64, Integer::I8],
            vec![vec![], vec![0], vec![1], vec![2]],
            vec![vec![1, 2], vec![0], vec![0]],
        ),
    ];
    for (case, (locals, prefix, variants, conflicts)) in cases.into_iter().enumerate() {
        let values: Vec<L> = locals.into_iter().map(|i| scalar(&dl, i)).collect();
        let refs: Vec<&L> = values.iter().collect();
        let locals: IndexVec<usize, &&L> = refs.iter().collect();
        let pv: Vec<L> = prefix.into_iter().map(|i| scalar(&dl, i)).collect();
        let pr: Vec<&L> = pv.iter().collect();
        let prefix: IndexVec<usize, &&L> = pr.iter().collect();
        let variants: IndexVec<usize, IndexVec<usize, usize>> = variants
            .into_iter()
            .map(|x| x.into_iter().collect())
            .collect();
        let mut matrix = BitMatrix::new(values.len(), values.len());
        for (a, row) in conflicts.into_iter().enumerate() {
            for b in row {
                matrix.insert(a, b);
            }
        }
        let layout = LayoutCalculator::new(&dl)
            .layout_of_coroutine(&locals, prefix, &variants, &matrix, |s| {
                Box::leak(Box::new(&*Box::leak(Box::new(L::scalar(&dl, s)))))
            })
            .unwrap();
        let FieldsShape::Arbitrary {
            offsets,
            in_memory_order,
        } = layout.fields
        else {
            panic!()
        };
        println!(
            "case{} {} {} {:?} {:?}",
            case,
            layout.size.bytes(),
            layout.align.bytes(),
            offsets.iter().map(|s| s.bytes()).collect::<Vec<_>>(),
            in_memory_order.raw
        );
        let Variants::Multiple { variants, .. } = layout.variants else {
            panic!()
        };
        for (i, v) in variants.iter_enumerated() {
            // rustc_abi exposes the permutation only through Debug, so this pinned
            // comparison adapter reads that field without reconstructing it from offsets.
            let debug = format!("{v:?}");
            let order = debug
                .split_once("fields_in_memory_order: ")
                .unwrap()
                .1
                .split_once(']')
                .unwrap()
                .0
                .to_owned()
                + "]";
            println!(
                "v{} {} {:?} {}",
                i,
                v.size.bytes(),
                v.field_offsets
                    .iter()
                    .map(|s| s.bytes())
                    .collect::<Vec<_>>(),
                order
            );
        }
    }
}

import Lean

namespace Miri.Input.ConcreteFieldShuffle

private structure Generator where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32

private def rotate (value : UInt32) (bits : UInt32) : UInt32 :=
  (value <<< bits) ||| (value >>> (32-bits))

private def next (state : Generator) : UInt32 × Generator :=
  let value := rotate (state.b*5) 7 * 9
  let c := state.c ^^^ state.a
  let d := state.d ^^^ state.b
  (value,⟨state.a ^^^ d,state.b ^^^ c,c ^^^ (state.b <<< 9),rotate d 11⟩)

private def splitMix (state : UInt64) : UInt64 × UInt64 :=
  let state := state+0x9e3779b97f4a7c15
  let value := (state ^^^ (state >>> 30))*0xbf58476d1ce4e5b9
  let value := (value ^^^ (value >>> 27))*0x94d049bb133111eb
  (value ^^^ (value >>> 31),state)

private def seed (value : UInt64) : Generator :=
  let (first,state) := splitMix value
  let (second,_) := splitMix state
  ⟨first.toUInt32,(first >>> 32).toUInt32,second.toUInt32,(second >>> 32).toUInt32⟩

private def sample (state : Generator) (bound : Nat) : Nat × Generator := Id.run do
  let (word,state) := next state
  let product := word.toNat*bound
  let mut result := product/2^32
  let low := product%2^32
  let mut state := state
  if low > 2^32-bound then
    let (word,fresh) := next state
    state := fresh
    let high := (word.toNat*bound)/2^32
    if low+high ≥ 2^32 then result := result+1
  return (result,state)

/-- rustc's randomized field order depends on the exact pinned Rand shuffle,
including its chunked index sampler; Fisher–Yates with another sampler differs. -/
def shuffle (values : Array α) (seedValue : UInt64) : Except String (Array α) := do
  let mut values := values
  let mut state := seed seedValue
  let mut chunk := 0
  let mut remaining := 1
  for i in [:values.size] do
    if remaining == 0 then
      let mut product := i+1
      let mut count := 1
      for _ in [:32] do
        let candidate := product*(i+1+count)
        if candidate ≥ 2^32 then break
        product := candidate
        count := count+1
      let (value,fresh) := sample state product
      chunk := value
      state := fresh
      remaining := count
    remaining := remaining-1
    let index := if remaining == 0 then chunk else chunk%(i+1)
    if remaining != 0 then chunk := chunk/(i+1)
    if left : i < values.size then
      if right : index < values.size then
        values := values.swap i index left right
      else throw "field shuffle sampled index invariant"
    else throw "field shuffle iteration index invariant"
  return values
end Miri.Input.ConcreteFieldShuffle

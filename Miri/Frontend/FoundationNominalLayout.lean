import Miri.Frontend.FoundationPhysicalTypes

/-! A deliberately narrow declaration-driven nominal layout component. No nominal
TypeNode/trait fact is claimed. The rules are pinned rustc_abi/layout.rs
layout_of_univariant_biased (one scalar-pair field and trailing alignment-one
ZSTs), and layout_of_enum (two one-field variants, null niche at offset zero).
All seeds come from declaration repr material and recursively computed fields.
The tagged candidate is strictly larger for this subset: its nonzero tag prefix
precedes a two-word, word-aligned payload. No layout answer catalog is consumed. -/
namespace Miri.Frontend.Foundation
open Lean
private def field := Json.getObjVal?
private def nat (j : Json) (key : String) := j.getObjValAs? Nat key
private def string (j : Json) (key : String) := j.getObjValAs? String key
private def array (j : Json) (key : String) := j.getObjValAs? (Array Json) key

private structure NominalField where
  layout : Input.Layout
  concrete : Option ConcreteType := none

private def addSeed (a b : Nat) : Nat := (UInt64.ofNat a + UInt64.ofNat b).toNat
private def fieldsAt (offsets : Array Nat) : Input.FieldShape :=
  ⟨.arbitrary, offsets.size, none, none, offsets, (List.range offsets.size).toArray⟩
private def mem : Input.BackendRepr :=
  ⟨.memory, some true, none, none, none, none, none, none, none⟩

private def reprSeed (repr : Json) (allowed : Array Nat) : Except String Nat := do
  unless allowed.contains (← nat repr "flags_bits") do throw "unsupported nominal repr flags"
  for key in #["align_bytes", "integer", "pack_bytes", "scalable_element"] do
    unless (← field repr key) == Json.null do throw "unsupported nominal repr modifier"
  nat repr "field_shuffle_seed"

private def nonnullPair (l : Input.Layout) : Except String Input.Layout := do
  let some b := l.backendRepresentation | throw "pointer backend absent"
  let some a := b.first | throw "nonnull subset requires scalar pair"
  let some z := b.second | throw "pointer metadata absent"
  let w := a.primitive.sizeBytes
  unless b.kind == .scalarPair && a.primitive.kind == .pointer &&
      a.primitive.addressSpace == some 0 && a.validRange == some (0, 2^(w*8)-1) &&
      z.primitive.kind == .pointer && z.validRange == some (1, 2^(w*8)-1) &&
      l.sizeBytes == some (2*w) && b.secondOffsetBytes == some w do
    throw "unsupported nonnull source pattern layout"
  let a := { a with validRange := some (1, 2^(w*8)-1) }
  return { l with
    fields := some (fieldsAt #[0]), fieldOffsetsBytes := (.explicit #[0]),
    backendRepresentation := some { b with first := some a },
    largestNiche := some ⟨0, a.primitive, (1, 2^(w*8)-1)⟩ }

private def wrapperLayout (empty : Input.Layout) (seed : Nat)
    (fs : Array Input.Layout) : Except String Input.Layout := do
  let combined := fs.foldl (fun s f => addSeed s f.randomizationSeed) seed
  if fs.isEmpty then return { empty with randomizationSeed := combined }
  let some first := fs[0]? | throw "missing wrapper field"
  let some backend := first.backendRepresentation | throw "missing wrapper backend"
  let some size := first.sizeBytes | throw "missing wrapper size"
  unless backend.kind == .scalarPair && size > 0 &&
      (first.abiAlignBytes.getD 0) > 1 do throw "unsupported nominal non-ZST field"
  for f in fs.extract 1 fs.size do
    unless f.sizeBytes == some 0 && f.abiAlignBytes == some 1 && !f.uninhabited do
      throw "unsupported nominal trailing field"
  let offsets := #[0] ++ Array.replicate (fs.size-1) size
  return { first with
    fields := some (fieldsAt offsets), fieldOffsetsBytes := (.explicit offsets),
    randomizationSeed := combined }

private def nicheResult (seed : Nat) (ok err : Input.Layout) : Except String Input.Layout := do
  let some b := err.backendRepresentation | throw "missing error backend"
  let some a := b.first | throw "missing error data scalar"
  let some z := b.second | throw "missing error metadata scalar"
  let w := a.primitive.sizeBytes
  let some ob := ok.backendRepresentation | throw "missing success backend"
  let some os := ob.scalar | throw "unsupported success payload"
  unless w > 0 && w ≤ 16 && err.sizeBytes == some (2*w) && err.abiAlignBytes == some w &&
      err.unadjustedAbiAlignBytes == some w && b.kind == .scalarPair &&
      b.secondOffsetBytes == some w && a.primitive.kind == .pointer &&
      a.primitive.addressSpace == some 0 && z.primitive.kind == .pointer &&
      z.primitive.addressSpace == some 0 && z.primitive.sizeBytes == w &&
      a.validRange == some (1, 2^(w*8)-1) && z.validRange == some (1, 2^(w*8)-1) &&
      ok.sizeBytes == some w && ok.abiAlignBytes == some w &&
      ob.kind == .scalar && os.primitive.kind == .integer && os.primitive.signed == some true &&
      os.validRange == some (0, 2^(w*8)-1) && !ok.uninhabited && !err.uninhabited do
    throw "unsupported two-variant niche layout"
  let tag := { a with validRange := some (0, 2^(w*8)-1) }
  let variants : Array Input.LayoutVariant := #[
    ⟨fieldsAt #[w], none, 0, 2*w, mem, #[w], false⟩,
    ⟨fieldsAt #[0], err.largestNiche, 1, 2*w, b, #[0], false⟩]
  let combined := addSeed seed (addSeed (addSeed seed ok.randomizationSeed)
    (addSeed seed err.randomizationSeed))
  return { err with
    fields := some (fieldsAt #[0]), fieldOffsetsBytes := (.explicit #[0]),
    variantsLayout := some ⟨.multiple, none, some tag,
      some ⟨.niche, some 1, some (0,0), some 0⟩, some 0, variants⟩,
    variantsKind := some .multiple, backendRepresentation := some mem,
    backendReprKind := some .memory, largestNiche := none, randomizationSeed := combined }

/-- Compute physical rows directly from finite source declaration/type material.
The nominal subset is empty structs, single-pair wrappers with trailing ZSTs,
and the two-field-variant null-niche enum described above. This does not extend
ConcreteType or manufacture nominal runtime identities/compiler facts. -/
def sourceNominalPhysicalLayout (d : Document) (typeId : Nat) (parameters : Array Nat := #[]) : Except String Input.Layout := do
  let empty ← physicalLayoutOfDocument d (.tuple #[])
  let mut actual := #[]
  for id in parameters do actual := actual.push (← go 256 empty #[] id)
  return (← go 256 empty actual typeId).layout
where
  go (fuel : Nat) (empty : Input.Layout) (args : Array NominalField) (id : Nat) :
      Except String NominalField := do
    let .succ fuel := fuel | throw "nominal source recursion exhausted"
    let some row := d.types[id]? | throw "nominal type source absent"
    let s ← field row "shape"
    match ← string s "kind" with
    | "param" =>
      let some f := args[← nat s "index"]? | throw "nominal substitution absent"
      return f
    | "raw_pointer" =>
      let p ← go fuel empty args (← nat s "pointee")
      let some p := p.concrete | throw "nominal pointer pointee unsupported"
      let mutable ← s.getObjValAs? Bool "mutable"
      let t := ConcreteType.pointer (if mutable then "raw_pointer_mut" else "raw_pointer_const") p
      return ⟨← physicalLayoutOfDocument d t, some t⟩
    | "pattern_type" =>
      unless (← string (← field s "pattern") "kind") == "not_null" do
        throw "unsupported nominal type pattern"
      return ⟨← nonnullPair (← go fuel empty args (← nat s "base")).layout, none⟩
    | "adt" =>
      let mut actual := #[]
      for a in ← array s "arguments" do
        unless (← string a "kind") == "type" do throw "unsupported nominal generic argument"
        actual := actual.push (← go fuel empty args (← nat a "type"))
      let definition ← nat s "definition"
      let some defn := d.definitions[definition]? | throw "nominal declaration absent"
      let adt ← field defn "adt"
      let variants ← array adt "variants"
      let repr ← field adt "representation"
      if (← string adt "kind") == "struct" then
        let seed ← reprSeed repr #[0,4,8]
        unless variants.size == 1 do throw "unsupported struct variants"
        let mut fs := #[]
        let some variant := variants[0]? | throw "struct variant absent"
        for f in ← array variant "fields" do
          fs := fs.push (← go fuel empty actual (← nat f "type")).layout
        return ⟨← wrapperLayout empty seed fs, none⟩
      else
        unless (← string adt "kind") == "enum" && variants.size == 2 do
          throw "unsupported nominal kind"
        let seed ← reprSeed repr #[0]
        let mut fs := #[]
        for i in [0:2] do
          let some v := variants[i]? | throw "enum variant absent"
          let disc ← field v "discriminant"
          unless (← nat v "index") == i && (← string disc "kind") == "relative" &&
              (← nat disc "distance") == i do throw "unsupported enum discriminant source"
          let fields ← array v "fields"
          unless fields.size == 1 do throw "unsupported enum variant fields"
          let some f := fields[0]? | throw "variant field absent"
          fs := fs.push (← go fuel empty actual (← nat f "type")).layout
        let some ok := fs[0]? | throw "success payload absent"
        let some err := fs[1]? | throw "error payload absent"
        return ⟨← nicheResult seed ok err, none⟩
    | _ =>
      let t ← instantiate #[] #[] (← typeExpr d id)
      return ⟨← physicalLayoutOfDocument d t, some t⟩
end Miri.Frontend.Foundation

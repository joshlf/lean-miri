import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceAbi
open Lean Miri Miri.Input Miri.Frontend.Foundation

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine catch MIR-use source")
  let document ← IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= decode)
  let world ← IO.ofExcept (compilerEntrySeed document)
  let some source := world.canonical.sourceMaterial | throw (IO.userError "source absent")
  let some physical := source.physical | throw (IO.userError "physical source absent")
  let some uses := source.mirUses | throw (IO.userError "MIR uses absent")
  let [function] := (source.declarations.filter (·.path == "std::panic::catch_unwind")).toList
    | throw (IO.userError "genuine function declaration absent")
  let [use] := (uses.declarations.filter (·.definition == function.definition)).toList
    | throw (IO.userError "genuine MIR-use declaration absent")
  let some body := use.body | throw (IO.userError "genuine optimized body absent")
  let ret ← IO.ofExcept (SourceParamAttrs.parameterUsage body 0)
  let arg ← IO.ofExcept (SourceParamAttrs.parameterUsage body 1)
  unless ret == ⟨false,false,true,true⟩ && arg == ⟨false,false,false,false⟩ do
    throw (IO.userError "actual catch MIR return/argument use differs from pinned visitor")
  -- Dereference-first uses affect the pointee, not indirect parameter storage.
  let indirect := {body with events := body.events.map fun event =>
    {event with kind := match event.kind with
      | .place place context => .place {place with firstProjection := some .deref} context
      | .callMove place => .callMove {place with firstProjection := some .deref}
      | .tailCall => .tailCall}}
  unless (← IO.ofExcept (SourceParamAttrs.parameterUsage indirect 0)) == ⟨false,false,true,false⟩ do
    throw (IO.userError "dereference-first use changed root parameter storage")
  let tail := {body with events := #[⟨0,0,.tailCall⟩]}
  unless (← IO.ofExcept (SourceParamAttrs.parameterUsage tail 1)) == ⟨false,false,true,true⟩ do
    throw (IO.userError "tail-call visitor did not conservatively mark argument")
  let root : SourceMirUses.Place := ⟨1,none⟩
  for (context,projection,expected) in [
      (SourceMirUses.Context.mutating .drop,none,SourceParamAttrs.Usage.mk true false false false),
      (.mutating .drop,some .other,⟨false,false,true,true⟩),
      (.nonMutating .sharedBorrow,none,⟨false,true,false,true⟩),
      (.nonMutating .rawBorrow,none,⟨false,false,true,true⟩),
      (.mutating .store,none,⟨false,false,true,false⟩)] do
    let control := {body with events := #[⟨0,0,.place {root with firstProjection := projection} context⟩]}
    unless (← IO.ofExcept (SourceParamAttrs.parameterUsage control 1)) == expected do
      throw (IO.userError "pinned place-context visitor distinction failed")
  match SourceParamAttrs.parameterUsage {body with phase := .known (.Runtime .PostCleanup)} 0 with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "nonoptimized source accepted for deduction")
  let [closure] := (physical.types.zipIdx |>.filterMap fun (type,index) => match type with
    | .closure closure => if physical.definitions[closure.definition]?.map (·.path) == some
        "std::rt::lang_start_internal::{closure#0}" then some index else none
    | _ => none).toList | throw (IO.userError "actual internal closure absent")
  let concrete ← IO.ofExcept (SourceTypes.instantiate physical #[] #[] closure)
  let (world,closure) ← IO.ofExcept (SourcePhysical.intern world concrete)
  let (world,isize) ← IO.ofExcept (SourcePhysical.intern world (.primitive "int" "isize"))
  let (world,callee) ← IO.ofExcept (SourceCompilerWorld.internItem source.declarations world
    ⟨function.definition,#[.Type closure,.Type isize]⟩)
  match SourceAbi.derive world callee #[] with
  | .error message =>
    unless message.startsWith "typed ABI indirect parameter 1 requires defining" do
      throw (IO.userError s!"return no-adjustment witness failed: {message}")
  | .ok (_,abi) =>
    unless use.compilation.any (fun c => c.optimization == .no || c.incremental) do
      throw (IO.userError "unproven external enabled deduction accepted")
    let expected : AbiPassMode := ⟨.indirect,#[⟨670,16,some 8,.none⟩],none,none,none,some .pointer⟩
    unless abi.returnValue.mode == expected do throw (IO.userError "actual return indirect mode differs")
  let absentSource := {source with mirUses := none}
  let absent := {world with canonical := {world.canonical with sourceMaterial := some absentSource}}
  match SourceAbi.derive absent callee #[] with
  | .error message =>
    unless message.startsWith "typed ABI indirect parameter 0 requires defining-crate MIR deduction evidence" do
      throw (IO.userError "missing material did not reject at return evidence demand")
  | .ok _ => throw (IO.userError "missing MIR-use capability accepted")
  let absentDeclaration := {source with mirUses := some {uses with declarations := uses.declarations.filter (·.definition != function.definition)}}
  let absent := {world with canonical := {world.canonical with sourceMaterial := some absentDeclaration}}
  match SourceAbi.derive absent callee #[] with
  | .error "typed ABI indirect MIR-use declaration absent/ambiguous" => pure ()
  | _ => throw (IO.userError "omitted MIR-use declaration confused with observed no-MIR")
  let noExternalBody := {uses with declarations := uses.declarations.map fun row =>
    if row.definition == function.definition then {row with body := none,compilation := none} else row}
  let noExternalBody := {source with mirUses := some noExternalBody}
  let noExternalBody := {world with canonical := {world.canonical with sourceMaterial := some noExternalBody}}
  match SourceAbi.derive noExternalBody callee #[] with
  | .error "typed ABI indirect parameter 0 requires defining MIR availability evidence" => pure ()
  | _ => throw (IO.userError "unencoded external MIR confused with defining no-MIR")
  IO.println "actual optimized MIR-use visitor and gate-independent return witness passed"

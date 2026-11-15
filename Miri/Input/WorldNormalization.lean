import Miri.Input.GenericSyntax
import Miri.Input.GenericInstantiationWorld
import Miri.Input.BinderRegions

/-! Material normalization uses rustc's exact result. Constructed syntax may
normalize structurally only when no compiler selection is required. -/
namespace Miri.Input.WorldNormalization
open GenericSubstitution TypeArena

private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error

private def residual (world : World) (source : TypeNode) : Except String TypeId := do
  let some facts := source.compilerFacts | throw "material normalization facts absent"
  unless facts.typingEnvironment == "fully_monomorphized" do
    throw "material normalization environment mismatch"
  let some (_,some target) := facts.typeQueries.find? (·.1 == "normalized")
    | throw "missing explicitly residual material normalization result"
  unless target < world.materialTypes.size do
    throw "residual normalization result escapes the material prefix"
  let _ ← world.lookupType target
  pure target

private def normalizeRegion (fuel : Nat) (region : MIR.Region) : WorldM MIR.Region := do
  let world ← get
  let term ← lift (GenericInstantiationWorld.ofRegion world region)
  let term ← lift (GenericSyntax.eraseFreeRegions fuel term)
  lift (GenericSyntax.validateClosed fuel term)
  lift (GenericInstantiationWorld.resolveRegion world term)

def normalizeTerm (_context : Unit) (_work fuel : Nat)
    (term : Term) : WorldM Term := do
  let term ← lift (GenericSyntax.eraseFreeRegions fuel term)
  lift (BinderRegions.requireAliasFree fuel term)
  pure term

/-- Normalize an instantiated source field expression, then intern the result
in this execution's current universe. All newly created child IDs are retained. -/
def resolveNormalizedTerm (context : Unit) (work fuel : Nat)
    (term : Term) : WorldM TypeId := do
  GenericInstantiationWorld.resolveType fuel (← normalizeTerm context work fuel term)

private def normalizeConstant (context : Unit) (fuel work : Nat)
    (id : TypeConstantId) : WorldM TypeConstantId := do
  let term ← lift (GenericInstantiationWorld.ofConstant (← get) fuel id)
  let result ← normalizeTerm context work fuel term
  GenericInstantiationWorld.resolveConstant fuel result

/-- Material query views are honored before lookup. Constructed normalization
observes every interning update. -/
private abbrev NormalizeM := StateT (Std.HashMap TypeId TypeId) WorldM

private def normalizeCached (context : Unit) (work : Nat) :
    Nat → TypeId → NormalizeM TypeId
  | 0, _ => throw "execution-world normalization traversal exhausted"
  | fuel + 1, id => do
    if let some result := (← get)[id]? then return result
    let result ← do
      let world ← liftM (get : WorldM World)
      let view ← lift (world.lookupType id)
      if let .material source := view then
        if let some queryView := source.layoutQueryInputTypeId then
          if queryView != id then
            unless queryView < world.materialTypes.size do
              throw "material normalization query view escapes its prefix"
            return ← normalizeCached context work fuel queryView
        return ← lift (residual world source)
      let .constructed constructor := view | throw "expected constructed type"
      if let .alias .. := constructor then
        throw "constructed alias has no exact rustc normalization result"
      if let .dynamic _ := constructor then
        unless ← lift (GenericInstantiationWorld.supportsTypeReification world (fuel + 1) id) do
          throw "dynamic normalization requires lossless child source"
        let term ← lift (GenericInstantiationWorld.ofType world (fuel + 1) id)
        match BinderRegions.requireAliasFree (fuel + 1) term with
        | .error error => throw error
        | .ok () => pure ()
        let term ← lift (BinderRegions.eraseAndAnonymize (fuel + 1) term)
        return ← liftM (GenericInstantiationWorld.resolveType (fuel + 1) term)
      if let .functionPointer signature := constructor then
        unless signature.variables.isEmpty do
          -- Bound children are open in isolation. Normalize the whole binder.
          unless ← lift (GenericInstantiationWorld.supportsTypeReification world (fuel + 1) id) do
            throw "constructed binder contains an unsupported raw constructor family"
          let raw ← lift (GenericInstantiationWorld.ofType world (fuel + 1) id)
          match BinderRegions.requireAliasFree (fuel + 1) raw with
          | .error error => throw error
          | .ok () => pure ()
          let normalized ← lift (BinderRegions.eraseAndAnonymize (fuel + 1) raw)
          return ← liftM (GenericInstantiationWorld.resolveType (fuel + 1) normalized)
      let argument := fun arg => do
        match arg with
        | .Type child => return MIR.GenericArg.Type (← normalizeCached context work fuel child)
        | .Lifetime region => return .Lifetime (← liftM (normalizeRegion (fuel + 1) region))
        | .Const constant => return .Const (← liftM (normalizeConstant context (fuel + 1) work constant))
      let normalized ← match constructor with
        | .rawPointer child mutability =>
          pure (.rawPointer (← normalizeCached context work fuel child) mutability)
        | .reference child mutability region =>
          pure (.reference (← normalizeCached context work fuel child) mutability
            (← liftM (normalizeRegion (fuel + 1) region)))
        | .functionPointer signature => do
          let inputs ← signature.inputs.mapM (normalizeCached context work fuel)
          let output ← normalizeCached context work fuel signature.output
          pure (.functionPointer {signature with inputs, output})
        | .patternType base pattern => do
          let pattern ← liftM (pattern.mapConstants (normalizeConstant context (fuel + 1) work) (fuel + 1))
          pure (.patternType (← normalizeCached context work fuel base) pattern)
        | .slice child => pure (.slice (← normalizeCached context work fuel child))
        | .tuple children => pure (.tuple (← children.mapM (normalizeCached context work fuel)))
        | .array child length => pure (.array (← normalizeCached context work fuel child)
            (← liftM (normalizeConstant context (fuel + 1) work length)))
        | .adt definition args => pure (.adt definition (← args.mapM argument))
        | .functionDefinition definition args variables => do
          unless variables.isEmpty do throw "execution-world normalization excludes nonempty FnDef binders"
          pure (.functionDefinition definition (← args.mapM argument) variables)
        | .closure definition args => pure (.closure definition (← args.mapM argument))
        | .coroutineClosure definition args => pure (.coroutineClosure definition (← args.mapM argument))
        | .coroutine definition args => pure (.coroutine definition (← args.mapM argument))
        | other => pure other
      liftM (World.internType normalized)
    modify fun memo => memo.insert id result
    pure result

/-- The memo exists only for this query. It records normalized syntax IDs, is
not retained in World, and prevents repeated visits to shared constructor DAGs. -/
def normalizeType (context : Unit) (work fuel : Nat) (id : TypeId) :
    WorldM TypeId := do
  let (result,_) ← (normalizeCached context work fuel id).run {}
  pure result

end Miri.Input.WorldNormalization

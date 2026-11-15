import Miri.Input.SourceMirPlaces

/-! Generic typed source rvalues and projection facts. This constructs fixed MIR
syntax only. Unsize/vtable/instance operations remain actual interpreter demands;
no method winner, function allocation or vtable identity is selected here. -/
namespace Miri.Input.SourceMirRvalues
structure Context where
  world : SourceCompilerWorld.World
  localTypes : Array Nat
  types : Array (Option Nat)
  definitions : Array (Option Nat)
  constant : SourceMir.Constant → Except String MIR.ConstOperand

def known (value : SourceMir.Operator α) : Except String α :=
  match value with | .known value => pure value | .unsupported tag => throw s!"Unsupported source MIR operator {tag}"
def place (c : Context) (p : SourceMir.Place) : Except String (MIR.Place × PlaceFact) :=
  SourceMirPlaces.lower c.world c.localTypes c.types p
private def shape (c : Context) (id : Nat) : Except String TypeShape := do
  let some node := c.world.canonical.types[id]? | throw "Invalid source rvalue type handle"
  return node.shape

def operand (c : Context) (op : SourceMir.Operand) : Except String (MIR.Operand × Nat × Array PlaceFact) := do
  match op with
  | .copy p =>
    let (p,fact) ← place c p
    return (.Copy p,fact.typeId,#[fact])
  | .move p =>
    let (p,fact) ← place c p
    return (.Move p,fact.typeId,#[fact])
  | .constant value =>
    let value ← c.constant value
    let .Val _ type := value.value
    return (.Constant value,type,#[])
  | .unsupported tag => throw s!"Unsupported source MIR operand {tag}"
private def operands (c : Context) (values : Array SourceMir.Operand) :
    Except String (Array MIR.Operand × Array Nat × Array PlaceFact) := do
  let mut result := #[]
  let mut types := #[]
  let mut facts := #[]
  for value in values do
    let (value,type,extra) ← operand c value
    result := result.push value; types := types.push type; facts := facts ++ extra
  return (result,types,facts)
private def arguments (c : Context) (values : Array SourceTypes.Argument) : Except String (Array MIR.GenericArg) :=
  values.mapM fun value => do
    let .type ref := value | throw "Unsupported source closure non-type argument"
    let some id := c.types[ref]?.join | throw "Invalid source closure argument not prepared"
    return .Type id

/-- The expected destination comes from the independently derived place path.
Aggregate/reference/unsize constructors check their source type annotations at
this boundary; runtime compiler leaves remain unresolved until demanded. -/
def lower (c : Context) (expected : Nat) (value : SourceMir.Rvalue) : Except String (MIR.Rvalue × Array PlaceFact) := do
  match value with
  | .use value retag =>
    let (value,type,facts) ← operand c value
    unless type == expected do throw "Invalid source Use/destination type mismatch"
    return (.Use value (if retag then .Yes else .No),facts)
  | .binary operator a b =>
    let (a,_,af) ← operand c a
    let (b,_,bf) ← operand c b
    return (.BinaryOp (← known operator) a b,af ++ bf)
  | .unary operator value =>
    let (value,_,facts) ← operand c value
    return (.UnaryOp (← known operator) value,facts)
  | .reference region borrow p =>
    let (p,fact) ← place c p
    let borrow ← known borrow
    unless borrow == .Shared do throw "Unsupported source mutable borrow recipe"
    match region with
    | .erased | .static => pure ()
    | _ => throw "Unsupported source reference region binder"
    let .reference pointee .Not .Erased ← shape c expected | throw "Invalid source reference destination type"
    unless pointee == fact.typeId do throw "Invalid source reference pointee type mismatch"
    -- Instance::instantiate_mir_and_normalize_erasing_regions erases the
    -- region, including a source static region, in the executable instance.
    return (.Ref .Erased borrow p,#[fact])
  | .aggregateTuple values =>
    let (values,types,facts) ← operands c values
    let .tuple fields ← shape c expected | throw "Invalid source tuple destination type"
    unless fields == types do throw "Invalid source tuple field types"
    return (.Aggregate .Tuple values,facts)
  | .aggregateClosure definition args values =>
    let some definition := c.definitions[definition]?.join | throw "Invalid source closure definition not prepared"
    let args ← arguments c args
    let (values,types,facts) ← operands c values
    let .closure actual actualArgs count ← shape c expected | throw "Invalid source closure aggregate destination type"
    unless actual == definition && actualArgs == args && count == values.size do
      throw "Invalid source closure aggregate identity/arguments/capture count"
    let some (.Type tupled) := args.back? | throw "Invalid source closure tupled upvars argument"
    let .tuple captures ← shape c tupled | throw "Invalid source closure tupled upvars type"
    unless captures == types do throw "Invalid source closure capture types"
    return (.Aggregate (.Closure definition args) values,facts)
  | .unsize value target source =>
    let (value,sourceType,facts) ← operand c value
    let some target := c.types[target]?.join | throw "Invalid source unsize target not prepared"
    unless target == expected do throw "Invalid source unsize target/destination type mismatch"
    match ← shape c sourceType,← shape c target with
    | .reference _ sourceMut _,.reference _ targetMut _
    | .rawPointer _ sourceMut,.rawPointer _ targetMut =>
      unless sourceMut == targetMut do throw "Unsupported source unsize mutability adjustment"
    | _,_ => throw "Unsupported source unsize pointer forms"
    return (.Cast (.PointerCoercion .Unsize (← known source)) value target,facts)
  | .discriminant p =>
    let (p,fact) ← place c p
    return (.Discriminant p,#[fact])
  | _ => throw "Unsupported typed source MIR rvalue"
end Miri.Input.SourceMirRvalues

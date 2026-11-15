import Miri.Frontend.FoundationPhysicalTypes

namespace Miri.Frontend.Foundation
/-- Compute a supported physical row from a demanded source type, optionally
instantiating a source template with explicitly supplied source type arguments.
This constructs no runtime TypeNode or compiler facts. -/
def sourceNominalPhysicalLayout (d : Document) (typeId : Nat)
    (parameters : Array Nat := #[]) : Except String Input.Layout := do
  let args ← parameters.mapM fun id => do instantiate #[] #[] (← typeExpr d id)
  physicalLayoutOfDocument d (← instantiate (args.map some) #[] (← typeExpr d typeId))
end Miri.Frontend.Foundation

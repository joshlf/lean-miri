import Miri.Frontend.FoundationLiteralProgram

/-! Source str slices retain the compiler's exact allocation graph reference and
metadata length. Shared library composition performs no byte-key allocation. -/
namespace Miri.Frontend.Foundation

def strLiteralProgram (document : Document) (definition : Nat) : Except String Input.LoweredProgram :=
  literalProgram document definition .str

end Miri.Frontend.Foundation

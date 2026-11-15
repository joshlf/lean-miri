import Miri.Frontend.FoundationLiteralExecute
import Miri.Frontend.FoundationStrLiteralProgram

/-! Observe both scalar components of the fixed str return value. The checked
memory read length comes from actual runtime metadata, never a supplied length. -/
namespace Miri.Frontend.Foundation

def runStrLiteral (prepared : Input.CompilerProviders.Prepared) (expected : Array UInt8) : Except String String :=
  FixedLiteralRun.runPrepared prepared expected .str

end Miri.Frontend.Foundation

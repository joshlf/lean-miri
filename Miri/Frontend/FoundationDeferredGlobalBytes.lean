import Miri.Input.CompilerGlobalBytes

/-! A deferred compiler byte-interner capability. This prepares only the exact
str layout identity used by configuration construction; it never attaches a
key catalog or changes memory readiness. The unchanged GlobalByteMachine.reserve
rejects every actual byte-interner demand while readiness remains false.
Existing source ConstValue allocations use imported global-root identities and
need not allocate new byte keys. This is not an empty dedup catalog. -/
namespace Miri.Frontend.Foundation

set_option autoImplicit false in
/-- Build the configuration's str view while leaving byte allocation unavailable.
Callers must retain the supplied memory unchanged and must not mark its byte
keys ready. A previously attached/partial catalog is rejected to avoid hiding
its evidence or silently replacing its state. -/
def deferredGlobalBytes {P E K : Type} (runtime : Input.RuntimeMetadata)
    (memory : Memory.MemoryState P E K) : Except String Input.CompilerGlobalBytes.Prepared := do
  let source := runtime.source.queries.globalBytes
  source.validateAvailability
  if source.evidenceAvailable then
    throw "deferred byte interner requires explicit unavailable evidence"
  if memory.byteGlobalKeysReady || !memory.byteGlobalKeys.isEmpty then
    throw "deferred byte interner requires unattached keys"
  let candidates := runtime.source.types.filter (·.shapeKind == .str)
  unless candidates.size == 1 do throw "deferred byte interner requires one exact str primitive"
  let some node := candidates[0]? | throw "deferred str primitive absent"
  unless source.strType == node.id do
    throw "deferred byte interner str identity disagrees with unavailable capability"
  let _ ← (runtime.lookup node.id).mapError toString
  -- Prepared's key array is unused by configuration/strLayout; only attach
  -- installs keys in memory. No attach call is performed on this path.
  return ⟨node.id, #[]⟩

end Miri.Frontend.Foundation

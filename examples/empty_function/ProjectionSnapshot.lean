import empty_function.IndirectProjection
namespace EmptyFunction.ProjectionSnapshot
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem other_lookup (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree) (query : AllocId) (different : query ≠ id) :
    (UnitRetag.replaceTree memory id entry tree).live[query]? =
      memory.live[query]? := by
  simp [UnitRetag.replaceTree,Std.ExtTreeMap.getElem?_insert,Ne.symm different]

theorem replace_info (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree)
    (live : memory.live[id]? = some (entry)) (query : AllocId) :
    (UnitRetag.replaceTree memory id entry tree).getAllocInfo query = memory.getAllocInfo query := by
  by_cases same : query = id
  · subst query
    simp [MemoryState.getAllocInfo,UnitRetag.replace_lookup,live]
    rfl
  · unfold MemoryState.getAllocInfo
    rw [other_lookup memory id entry tree query same]
    rfl

theorem replace_live (memory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree)
    (live : memory.live[id]? = some (entry)) (query : AllocId) :
    (UnitRetag.replaceTree memory id entry tree).isAllocLive query = memory.isAllocLive query := by
  have keys : (UnitRetag.replaceTree memory id entry tree).live.contains query =
      memory.live.contains query := by
    rw [Std.ExtTreeMap.contains_eq_isSome_getElem?,Std.ExtTreeMap.contains_eq_isSome_getElem?]
    by_cases same : query = id
    · subst query
      simp [UnitRetag.replace_lookup,live]
    · rw [other_lookup memory id entry tree query same]

  unfold MemoryState.isAllocLive
  rw [keys]
  rfl

theorem offset_congr (pointers : EmptyFunction.CanonicalDictionaries.Pointers) (before after : State)
    (addresses : after.machine.user.addresses = before.machine.user.addresses)
    (info : ∀ id, after.machine.memory.getAllocInfo id = before.machine.memory.getAllocInfo id)
    (live : ∀ id, after.machine.memory.isAllocLive id = before.machine.memory.isAllocLive id)
    (place : MemPlace Provenance) (amount : Size) (mode : OffsetMode) (metadata : MemPlaceMeta Provenance) :
    EvalProjectionMachine.memoryOffset pointers after place amount mode metadata =
      EvalProjectionMachine.memoryOffset pointers before place amount mode metadata := by
  have infos : after.machine.memory.getAllocInfo = before.machine.memory.getAllocInfo := funext info
  have living : after.machine.memory.isAllocLive = before.machine.memory.isAllocLive := funext live
  unfold EvalProjectionMachine.memoryOffset
  rw [addresses,infos,living]
end EmptyFunction.ProjectionSnapshot

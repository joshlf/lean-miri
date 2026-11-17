import Miri.Input.LocalValidation

namespace Miri.Input

private structure ReferenceBounds where
  types : Nat
  allocations : Nat
  instances : Nat
  spans : Nat
  definitions : Nat
  constants : Nat
  bodies : Nat
  predicates : Nat

private def checkId (count id : Nat) (path kind : String) : Except String Unit := do
  unless id < count do throw s!"{path}: dangling {kind} reference {id}"

private def boundRegion (b : ReferenceBounds) (path : String) : MIR.BoundRegionKind → Except String Unit
  | .Named id => checkId b.definitions id path "definition"
  | .Anon | .NamedForPrinting _ | .ClosureEnv => pure ()

private def boundVariable (b : ReferenceBounds) (path : String) : MIR.BoundVariableKind → Except String Unit
  | .Type (.Param id) => checkId b.definitions id path "definition"
  | .Region region => boundRegion b path region
  | .Type .Anon | .Const => pure ()

private def region (b : ReferenceBounds) (path : String) : MIR.Region → Except String Unit
  | .Bound _ _ kind | .Placeholder _ _ kind => boundRegion b path kind
  | .LateParameter scope kind => do
    checkId b.definitions scope path "definition"
    match kind with
    | .Named id => checkId b.definitions id path "definition"
    | .Anon _ | .NamedAnon _ _ | .ClosureEnv => pure ()
  | .EarlyParameter _ _ | .Static | .InferenceVariable _ | .Erased | .Error => pure ()

private def genericArgs (b : ReferenceBounds) (path : String) (args : Array MIR.GenericArg) : Except String Unit := do
  for (arg, index) in args.toList.zipIdx do
    match arg with
    | .Type id => checkId b.types id s!"{path}[{index}]" "type"
    | .Const id => checkId b.constants id s!"{path}[{index}]" "type constant"
    | .Lifetime value => region b s!"{path}[{index}]" value

private def boundVariables (b : ReferenceBounds) (path : String) (variables : Array MIR.BoundVariableKind) : Except String Unit := do
  for (binder, index) in variables.toList.zipIdx do
    boundVariable b s!"{path}[{index}]" binder

private def signature (b : ReferenceBounds) (path : String) (value : FunctionSignature) : Except String Unit := do
  for (input, index) in value.inputs.toList.zipIdx do
    checkId b.types input s!"{path}.inputs[{index}]" "type"
  checkId b.types value.output s!"{path}.output" "type"

private partial def pattern (b : ReferenceBounds) (path : String) : CompilerPattern → Except String Unit
  | .range start finish => do
    checkId b.constants start s!"{path}.start" "type constant"
    checkId b.constants finish s!"{path}.end" "type constant"
  | .or values => do
    for (value, index) in values.toList.zipIdx do pattern b s!"{path}.patterns[{index}]" value
  | .notNull => pure ()

private def typeShape (b : ReferenceBounds) (path : String) : TypeShape → Except String Unit
  | .adt data => do
    checkId b.definitions data.definition s!"{path}.def_id" "definition"
    genericArgs b s!"{path}.generic_args" data.args
    for (variant, vi) in data.variants.toList.zipIdx do
      for (field, fi) in variant.fields.toList.zipIdx do
        checkId b.types field.typeId s!"{path}.variants[{vi}].fields[{fi}].type" "type"
  | .foreign definition => checkId b.definitions definition s!"{path}.def_id" "definition"
  | .array element length _ => do
    checkId b.types element s!"{path}.element" "type"
    checkId b.constants length s!"{path}.length" "type constant"
  | .patternType base value => do
    checkId b.types base s!"{path}.base" "type"
    pattern b s!"{path}.pattern" value
  | .slice element => checkId b.types element s!"{path}.element" "type"
  | .rawPointer pointee _ => checkId b.types pointee s!"{path}.pointee" "type"
  | .reference pointee _ lifetime => do
    checkId b.types pointee s!"{path}.pointee" "type"
    region b s!"{path}.region" lifetime
  | .functionDefinition definition args sig variables => do
    checkId b.definitions definition s!"{path}.def_id" "definition"
    genericArgs b s!"{path}.generic_args" args
    signature b s!"{path}.signature" sig
    boundVariables b s!"{path}.bound_variables" variables
  | .functionPointer sig variables => do
    signature b s!"{path}.signature" sig
    boundVariables b s!"{path}.bound_variables" variables
  | .unsafeBinder inner variables => do
    checkId b.types inner s!"{path}.inner" "type"
    boundVariables b s!"{path}.bound_variables" variables
  | .dynamicTraitObject predicates principal lifetime => do
    for (id, index) in predicates.toList.zipIdx do
      checkId b.predicates id s!"{path}.predicates[{index}]" "predicate"
    if let some id := principal then checkId b.predicates id s!"{path}.principal_predicate" "predicate"
    region b s!"{path}.region" lifetime
  | .closure definition args _ | .coroutineClosure definition args
  | .coroutine definition args | .alias _ definition args => do
    checkId b.definitions definition s!"{path}.def_id" "definition"
    genericArgs b s!"{path}.generic_args" args
  | .tuple elements => do
    for (id, index) in elements.toList.zipIdx do
      checkId b.types id s!"{path}.elements[{index}]" "type"
  | .bool | .char | .int _ | .uint _ | .float _ | .str | .never => pure ()

private def typeConstant (b : ReferenceBounds) (path : String) : MIR.TypeConst → Except String Unit
  | .Param _ _ declaredType => do
    if let some id := declaredType then checkId b.types id s!"{path}.type" "type"
  | .Alias _ _ definition args => do
    checkId b.definitions definition s!"{path}.def_id" "definition"
    genericArgs b s!"{path}.generic_args" args
  | .Value ty tree => do
    checkId b.types ty s!"{path}.type" "type"
    checkId tree.nodes.size tree.root s!"{path}.value.root" "valtree node"
    for (node, index) in tree.nodes.toList.zipIdx do
      match node with
      | .Branch children =>
        for (id, ci) in children.toList.zipIdx do
          checkId b.constants id s!"{path}.value.nodes[{index}].elements[{ci}]" "type constant"
      | .Leaf _ _ => pure ()
  | .Expr _ args => genericArgs b s!"{path}.arguments" args
  | .InferVar _ | .InferFresh _ | .Bound _ _ | .Placeholder _ _ | .Error => pure ()

private def instanceKind (b : ReferenceBounds) (path : String) : Interpreter.CallInstanceKind → Except String Unit
  | .Item id | .Intrinsic id | .LlvmIntrinsic id | .Virtual id _ => checkId b.definitions id path "definition"
  | .Shim shim => do
    checkId b.definitions shim.defId s!"{path}.def_id" "definition"
    match shim with
    | .ClosureOnce _ closure _ => checkId b.definitions closure s!"{path}.closure_def_id" "definition"
    | .FnPtr _ ty | .Clone _ ty | .FnPtrAsPtr _ ty | .FnPtrFromPtr _ ty
    | .AsyncDropGlueCtor _ ty | .AsyncDropGlue _ ty => checkId b.types ty s!"{path}.type" "type"
    | .FutureDropPoll _ proxy impl => do
      checkId b.types proxy s!"{path}.proxy_coroutine_type" "type"
      checkId b.types impl s!"{path}.implementation_coroutine_type" "type"
    | .DropGlue _ ty =>
      if let some id := ty then checkId b.types id s!"{path}.drop_type" "type"
    | .VTable _ | .Reify _ _ | .ConstructCoroutineInClosure _ _ | .ThreadLocal _ => pure ()

private def sourceInfo (b : ReferenceBounds) (path : String) (value : SourceInfo) : Except String Unit :=
  checkId b.spans value.spanId s!"{path}.span" "span"

private def promoted (b : ReferenceBounds) (path : String) (values : Array PromotedBody) : Except String Unit := do
  for (value, index) in values.toList.zipIdx do
    if let some id := value.bodyId then checkId b.bodies id s!"{path}[{index}].body" "body"

private def memory (b : ReferenceBounds) (path : String) (value : AllocationMemory) : Except String Unit := do
  for (relocation, index) in value.relocations.toList.zipIdx do
    checkId b.allocations relocation.target s!"{path}.relocations[{index}].target" "allocation"

private def validateExtraReferences (types : Array TypeNode) (instances : Array InstanceNode) : Except String Unit := do
  for node in instances do
    if node.kind == .virtualDispatchTarget then
      let some ty := node.virtualIdentity |
        throw s!"instances[{node.id}].virtual_identity: virtual identity lacks its source function type"
      let some functionType := types[ty]? |
        throw s!"instances[{node.id}].virtual_identity.function_type: missing compiler function type"
      unless functionType.shapeKind == .functionPointer || functionType.shapeKind == .functionDefinition do
        throw s!"instances[{node.id}].virtual_identity.function_type: expected compiler function type"

private def catalogSignature (b : ReferenceBounds) (path : String) (value : Catalog.Signature) : Except String Unit := do
  for id in value.inputs do checkId b.types id path "type"
  checkId b.types value.output path "type"

private def vtable (b : ReferenceBounds) (path : String) (value : VtableAllocation) : Except String Unit := do
  checkId b.types value.typeId s!"{path}.type" "type"
  for id in value.predicates do checkId b.predicates id path "predicate"
  if let some id := value.principalPredicate then checkId b.predicates id path "predicate"
  for entry in value.entries do
    if let some id := entry.instanceId then checkId b.instances id path "instance"
    if let some id := entry.allocationId then checkId b.allocations id path "allocation"
    if let some id := entry.traitDefinitionId then checkId b.definitions id path "definition"

private def externDeclaration (b : ReferenceBounds) (path : String) (value : Catalog.ExternDeclaration) : Except String Unit := do
  checkId b.definitions value.definition path "definition"
  checkId b.types value.typeId path "type"

private def foreignCandidate (b : ReferenceBounds) (path : String) (value : Catalog.ForeignCandidate) : Except String Unit := do
  checkId b.definitions value.definition path "definition"
  checkId b.spans value.span path "span"
  if let some id := value.instanceId then checkId b.instances id path "instance"

private def shimAbi (b : ReferenceBounds) (path : String) (value : Catalog.ShimAbi) : Except String Unit := do
  for id in value.inputTypes do checkId b.types id path "type"
  checkId b.types value.outputType path "type"

private def catalogs (b : ReferenceBounds) (q : Catalog.Queries) : Except String Unit := do
  checkId b.spans q.session.rootSpan "$.compiler_session.root_span" "span"
  if let some startup := q.runtime.startup then
    if let some (id, _) := startup.coreEscapeDefault then
      checkId b.definitions id "$.compiler_runtime_queries.startup.core_escape_default" "definition"
  for row in q.runtime.instances do
    checkId b.instances row.instanceId "$.compiler_runtime_queries.instances" "instance"
  let fs := q.runtime.foreignSymbols
  if let some rows := fs.exportedCandidates then
    for row in rows do foreignCandidate b "$.compiler_runtime_queries.foreign_symbols.exported_candidates" row
  if let some rows := fs.externDeclarations then
    for row in rows do externDeclaration b "$.compiler_runtime_queries.foreign_symbols.extern_declarations" row
  if let some rows := fs.selectedForeignFallbacks then
    for row in rows do
      match row with
      | .candidate value => foreignCandidate b "$.compiler_runtime_queries.foreign_symbols.selected_fallbacks" value
      | .ambiguous _ _ => pure ()
  if let some rows := fs.selectedExports then
    for row in rows do
      let path := "$.compiler_runtime_queries.foreign_symbols.selected_exports"
      match row with
      | .ambiguous _ _ => pure ()
      | .other _ _ definition inst =>
        checkId b.definitions definition path "definition"
        if let some id := inst then checkId b.instances id path "instance"
      | .static _ definition declaration allocation =>
        checkId b.definitions definition path "definition"
        externDeclaration b path declaration
        checkId b.allocations allocation path "allocation"
  for row in q.typeNames do
    for id in #[row.inputType, row.resultType] do checkId b.types id "$.compiler_type_name_constants" "type"
  for row in q.nativeSignatures do
    checkId b.instances row.instanceId "$.compiler_native_signatures" "instance"
    catalogSignature b "$.compiler_native_signatures" row.signature
  for row in q.panic do
    if let some id := row.definition then checkId b.definitions id "$.compiler_panic_queries" "definition"
  for row in q.retag do checkId b.definitions row.definition "$.compiler_retag_queries" "definition"

  for id in q.globalBytes.coveredAllocations do checkId b.allocations id "$.compiler_global_byte_queries.covered_allocations" "allocation"
  for row in q.globalBytes.candidates do
    for (_, allocation) in row.salts do
      if let some id := allocation then checkId b.allocations id "$.compiler_global_byte_queries.candidates" "allocation"
  if let some id := q.main.startLangItem then checkId b.definitions id "$.compiler_main.start_lang_item" "definition"
  if let some id := q.main.compilerEntry then checkId b.definitions id "$.compiler_main.compiler_entry" "definition"
  if let some row := q.main.compilerEntryType then checkId b.definitions row.definition "$.compiler_main.compiler_entry_type" "definition"
  for row in q.main.entries do
    let path := "$.compiler_main.entries"
    checkId b.definitions row.definition path "definition"
    checkId b.types row.signature.returnType path "type"
    checkId b.types row.signature.functionPointerType path "type"
    if let some start := row.signature.startResolution then
      checkId b.instances start.instanceId path "instance"
      checkId b.types start.functionType path "type"
  if let some rows := q.main.linkSections then
    for row in rows do
      let path := "$.compiler_main.link_sections"
      checkId b.definitions row.definition path "definition"
      checkId b.spans row.span path "span"
      checkId b.types row.typeId path "type"
      checkId b.allocations row.allocation path "allocation"
  let p := q.primitives
  for id in #[p.u8,p.u16,p.u32,p.u64,p.u128,p.i8,p.i16,p.i32,p.i64,p.i128,p.bool,
      p.pointerTagInteger,p.usize,p.isize,p.unit,p.unitPointerConst,p.unitPointerMut,
      p.immU8Pointer,p.immU8PointerPointer,p.typeNameResultType] do
    checkId b.types id "$.compiler_primitive_types" "type"
  for id in #[p.callerLocationType,p.orderingEnum] do
    if let some id := id then checkId b.types id "$.compiler_primitive_types" "type"
  if let some rows := q.namedTypes then
    for (_,id) in rows do checkId b.types id "$.compiler_named_types" "type"
  if let some rows := q.shimAbis then
    for row in rows do shimAbi b "$.compiler_shim_abis" row
  if let some rows := q.namedShimAbis then
    for row in rows do shimAbi b "$.compiler_named_shim_abis" row.recipe
  for rows in #[q.libcTypeLayouts,q.windowsTypeLayouts] do
    if let some rows := rows then
      for (_,id) in rows.entries do checkId b.types id "$.compiler_type_layouts" "type"
  if let some rows := q.namedConstants then
    for row in rows do
      let path := "$.compiler_named_constants"
      checkId b.instances row.instanceId path "instance"
      checkId b.types row.typeId path "type"
  if let some rows := q.namedStatics then
    for row in rows do
      let path := "$.compiler_named_statics"
      checkId b.definitions row.definition path "definition"
      checkId b.types row.typeId path "type"
      checkId b.allocations row.allocation path "allocation"

private def valueAllocations : MIR.ConstValue → Array Nat
  | .Scalar (.Ptr (.Allocation id _ _ _)) | .Slice id _ | .Indirect id _ => #[id]
  | _ => #[]

private def validateRequiredExecution (document : ImportDocument) : Except String Unit := do
  if document.selectedScope.isNone && document.compilerAllocIdWorld.isNone then return
  let roots := document.bodyRoots.filter fun root => match document.selectedScope with
    | none => true
    | some scope => scope.roots.any fun selected => selected.definitionId == root.definitionId && selected.defPath == root.defPath
  let mut pending : Array (Nat × Nat) := roots.flatMap fun root => #[(0, root.bodyId), (1, root.entryInstance)]
  let mut visited : Std.HashSet (Nat × Nat) := {}
  while !pending.isEmpty do
    let current := pending
    pending := #[]
    for (kind, id) in current do
      if visited.contains (kind,id) then continue
      visited := visited.insert (kind,id)
      if kind == 0 then
        let some body := document.bodies[id]? | throw "required body is absent"
        for constant in body.requiredConsts do
          let .Val value _ := constant.value
          pending := pending ++ (valueAllocations value).map (2, ·)
        for call in body.callEvidence do
          if let some call := call then
            if let some inst := call.instanceId then pending := pending.push (1, inst)
        for block in body.nodeFacts do
          for node in block do
            pending := pending ++ node.constantAllocations.map (2, ·)
            for tls in node.threadLocals do
              unless tls.info.isStatic && tls.info.threadLocal do
                throw s!"{body.sourcePath}: ThreadLocalRef lacks static/thread-local compiler evidence"
              let some image := tls.initializer | throw s!"{body.sourcePath}: ThreadLocalRef lacks initializer image"
              unless image.sizeBytes == tls.info.sizeBytes && image.alignBytes == tls.info.alignBytes do
                throw s!"{body.sourcePath}: TLS initializer size/alignment disagrees with static compiler query"
              for relocation in image.relocations do pending := pending.push (2, relocation.target)
      else if kind == 1 then
        let some inst := document.instances[id]? | throw "required instance is absent"
        if inst.kind == .identityOnly then
          throw s!"$.instances[{id}].kind: selected execution depends on a symbol identity that has no imported MIR body"
        if let some body := inst.bodyId then pending := pending.push (0, body)
      else
        let some allocation := document.allocations[id]? | throw "required allocation is absent"
        if let some data := allocation.data then
          match data with
          | .function function => pending := pending.push (1, function.instanceId)
          | .memory image =>
            for relocation in image.relocations do pending := pending.push (2, relocation.target)
          | .static value =>
            if let some image := value.initializer then
              for relocation in image.relocations do pending := pending.push (2, relocation.target)
          | .vtable value =>
            for entry in value.entries do
              if let some inst := entry.instanceId then pending := pending.push (1, inst)
              if let some allocation := entry.allocationId then pending := pending.push (2, allocation)
          | .typeId _ => pure ()

/-- Validate forward table references and graph relationships after row-local
invariants, including dense instance IDs, have been established by the parsers. -/
private def sourceLayout (b : ReferenceBounds) (path : String) (shape : TypeShape)
    (source : SourceTypeLayout) : Except String Unit := do
  checkId b.types source.normalizedType (path ++ ".normalized_type") "type"
  for id in source.closureUpvars do checkId b.types id (path ++ ".closure_upvars") "type"
  if let some id := source.definition then checkId b.definitions id (path ++ ".definition") "definition"
  if let some simd := source.simd then
    checkId b.types simd.element (path ++ ".simd.element") "type"
    unless simd.count > 0 && simd.count ≤ 32768 do throw (path ++ ": invalid SIMD lane count")
  if let some vectors := source.scalableVectors then
    unless vectors > 0 && vectors ≤ 8 && source.simd.isSome do
      throw (path ++ ": invalid scalable vector count")
  if let some coroutine := source.coroutine then
    for field in coroutine.traitFields do
      checkId b.types field.typeId (path ++ ".coroutine.trait_fields") "type"
    for id in coroutine.locals ++ coroutine.savedTypes ++ coroutine.prefix do checkId b.types id (path ++ ".coroutine") "type"
    unless coroutine.seed < 2^64 do throw (path ++ ": coroutine seed overflows u64")
    unless coroutine.savedTypes.size == coroutine.locals.size do throw (path ++ ": saved type count mismatch")
    unless coroutine.conflicts.size == coroutine.locals.size do throw (path ++ ": conflict matrix row count mismatch")
    for row in coroutine.variants ++ coroutine.conflicts do
      let mut seen : Std.HashSet Nat := {}
      for id in row do
        checkId coroutine.locals.size id (path ++ ".coroutine.local") "saved local"
        if seen.contains id then throw (path ++ ": duplicate saved local index")
        seen := seen.insert id
  match shape with
  | .adt data =>
    if data.kind == .enumKind then
      unless source.discriminants.size == data.variants.size do throw (path ++ ": enum discriminant count mismatch")
      for value in source.discriminants do
        unless -(2^127 : Int) ≤ value && value < (2^128 : Int) do throw (path ++ ": discriminant exceeds u128/i128 range")
  | .closure _ _ count =>
    unless count == source.closureUpvars.size do throw (path ++ ": closure capture type count mismatch")
  | _ => pure ()

def validateParsedTables (document : ImportDocument) : Except String Unit := do
  let b : ReferenceBounds := {
    types := document.types.size
    allocations := document.allocations.size
    instances := document.instances.size
    spans := document.spans.size
    definitions := document.definitions.size
    constants := document.typeConstants.size
    bodies := document.bodies.size
    predicates := document.predicates.size }
  let auxiliary := (document.coroutineCoverage.map (·.auxiliaryBodies)).getD #[]
  for (value, index) in auxiliary.toList.zipIdx do
    LocalValidation.validateBody value.body s!"$.compiler_coroutine_coverage.auxiliary_bodies[{index}].body"
    instanceKind b s!"$.compiler_coroutine_coverage.auxiliary_bodies[{index}].source_kind" value.sourceKind
  let bodyEntries := document.bodies.mapIdx (fun index value => (value, s!"$.bodies[{index}]")) ++
    auxiliary.mapIdx (fun index value => (value.body, s!"$.compiler_coroutine_coverage.auxiliary_bodies[{index}].body"))
  for (span, index) in document.spans.toList.zipIdx do
    checkId document.files.size span.file s!"$.spans[{index}].file" "file"
    checkId document.files.size span.expansionLocation.file s!"$.spans[{index}].expansion_location.file" "file"
  for (node, index) in document.types.toList.zipIdx do
    let path := s!"$.types[{index}]"
    typeShape b s!"{path}.shape" node.shape
    sourceLayout b s!"{path}.source_layout" node.shape node.sourceLayout
  for (value, index) in document.typeConstants.toList.zipIdx do
    typeConstant b s!"$.type_constants[{index}]" value
  for (value, index) in document.predicates.toList.zipIdx do
    let path := s!"$.predicates[{index}]"
    checkId b.definitions value.definitionId s!"{path}.def_id" "definition"
    genericArgs b s!"{path}.generic_args" value.genericArgs
    boundVariables b s!"{path}.bound_variables" value.boundVariables
    if let some id := value.projectionTerm then checkId b.types id s!"{path}.term" "type"
  for (value, index) in document.instances.toList.zipIdx do
    let path := s!"$.instances[{index}]"
    instanceKind b s!"{path}.instance_kind" value.instanceKind
    genericArgs b s!"{path}.generic_args" value.genericArgs
    if let some id := value.definitionId then checkId b.definitions id s!"{path}.def_id" "definition"
    if let some id := value.bodyId then
      checkId b.bodies id s!"{path}.body" "body"
      let some body := document.bodies[id]? | throw s!"{path}.body: body is absent"
      unless body.instanceId == value.id do throw s!"{path}.body: instance identity mismatch"
    promoted b s!"{path}.promoted_bodies" value.promotedBodies
    for entry in value.promotedBodies do
      if let some childId := entry.bodyId then
        let some child := document.bodies[childId]? | throw s!"{path}.promoted_bodies: body is absent"
        unless child.instanceId == value.id do
          throw s!"{path}.promoted_bodies: instance identity mismatch"

  for (value, index) in document.allocations.toList.zipIdx do
    let path := s!"$.allocations[{index}]"
    if let some image := value.memory then memory b path image
    if let some data := value.data then
      match data with
      | .memory image => memory b path image
      -- Dense IDs established by parseInstances make an in-bounds reference unique.
      | .function value => checkId b.instances value.instanceId s!"{path}.instance_id" "instance"
      | .static value =>
        checkId b.definitions value.definitionId s!"{path}.def_id" "definition"
        if let some image := value.initializer then memory b s!"{path}.initializer" image
      | .typeId id => checkId b.types id s!"{path}.type" "type"
      | .vtable value =>
        checkId b.types value.typeId s!"{path}.type" "type"
        if let some id := value.principalPredicate then checkId b.predicates id s!"{path}.principal_predicate" "predicate"
        for (id, pi) in value.predicates.toList.zipIdx do
          checkId b.predicates id s!"{path}.predicates[{pi}]" "predicate"
        for (entry, ei) in value.entries.toList.zipIdx do
          if let some id := entry.instanceId then checkId b.instances id s!"{path}.entries[{ei}].instance_id" "instance"
          if let some id := entry.allocationId then checkId b.allocations id s!"{path}.entries[{ei}].allocation" "allocation"
          if let some id := entry.traitDefinitionId then checkId b.definitions id s!"{path}.entries[{ei}].trait_def_id" "definition"
  for (value, path) in bodyEntries do
    for (entry, ei) in value.backtraceSpans.toList.zipIdx do
      checkId document.files.size entry.position.filename
        s!"{path}.backtrace_spans[{ei}].source_position.filename" "file"
    checkId b.instances value.instanceId s!"{path}.instance_id" "instance"
    for scope in value.sourceScopes do
      if let some inlined := scope.inlined then
        checkId b.instances inlined.instanceId path "instance"
        checkId b.spans inlined.callsiteSpanId path "span"
    for (evidence, blockIndex) in value.callEvidence.toList.zipIdx do
      if let some resolution := evidence then
        if let some id := resolution.instanceId then checkId b.instances id path "instance"
        let isLlvm := match resolution.instanceId.bind (document.instances[·]?) with
          | some node => match node.instanceKind with | .LlvmIntrinsic _ => true | _ => false
          | none => false
        match resolution.abi with
        | .normal =>
          unless resolution.kind != .llvmIntrinsic && !isLlvm do
            throw s!"{path}: LLVM intrinsic cannot carry an ordinary ABI"
        | .llvmIntrinsic =>
          unless resolution.kind == .llvmIntrinsic && isLlvm && resolution.dispatchSlot.isNone do
            throw s!"{path}: no-ABI call must resolve to an exact LLVM intrinsic"
          let some llvmInstance := resolution.instanceId.bind (document.instances[·]?) |
            throw s!"{path}: missing LLVM intrinsic identity"
          let .LlvmIntrinsic definition := llvmInstance.instanceKind |
            throw s!"{path}: invalid LLVM intrinsic identity"
          let some functionType := resolution.functionType |
            throw s!"{path}: missing LLVM source function type"
          let some sourceType := document.types[functionType]? |
            throw s!"{path}: missing LLVM function type definition"
          let .functionDefinition sourceDefinition sourceArgs _ _ := sourceType.shape |
            throw s!"{path}: LLVM source function type is not FnDef"
          unless sourceDefinition == definition && sourceArgs == llvmInstance.genericArgs do
            throw s!"{path}: LLVM function type differs from its canonical instance"
          let some block := value.mir.basicBlocks[blockIndex]? |
            throw s!"{path}: LLVM evidence has no source block"
          let operand ← match block.terminator.kind with
            | .Call operand .. | .TailCall operand .. => pure operand
            | _ => throw s!"{path}: LLVM evidence does not belong to a call"
          let operandType ← match operand with
            | .Constant constant =>
              let .Val _ ty := constant.value
              pure ty
            | .Copy place | .Move place => do
              let some facts := (value.nodeFacts[blockIndex]?).bind (·.back?) |
                throw s!"{path}: LLVM callee place has no terminator facts"
              let matching := facts.places.filter (·.place == place)
              let some first := matching[0]? |
                throw s!"{path}: LLVM callee place has no compiler type"
              unless matching.all (·.typeId == first.typeId) do
                throw s!"{path}: conflicting LLVM callee place types"
              pure first.typeId
            | .RuntimeChecks _ => throw s!"{path}: invalid LLVM callee operand"
          unless operandType == functionType do
            throw s!"{path}: LLVM evidence function type differs from MIR operand type"
    for facts in value.nodeFacts do
      for node in facts do
        for tls in node.threadLocals do
          checkId b.definitions tls.definition path "definition"
          if let some image := tls.initializer then memory b path image
    promoted b s!"{path}.promoted_bodies" value.promotedBodies
    for entry in value.promotedBodies do
      if let some childId := entry.bodyId then
        let some child := document.bodies[childId]? | throw s!"{path}.promoted_bodies: body is absent"
        unless child.instanceId == value.instanceId do
          throw s!"{path}.promoted_bodies: instance identity mismatch"
  for (value, index) in document.bodyRoots.toList.zipIdx do
    let path := s!"$.body_roots[{index}]"
    checkId b.bodies value.bodyId s!"{path}.body" "body"
    checkId b.instances value.entryInstance s!"{path}.entry_instance" "instance"
    let some body := document.bodies[value.bodyId]? | throw s!"{path}.body: body is absent"
    unless body.instanceId == value.entryInstance do throw s!"{path}.body: instance identity mismatch"
    checkId b.definitions value.definitionId s!"{path}.def_id" "definition"
    promoted b s!"{path}.promoted_bodies" value.promotedBodies
    for entry in value.promotedBodies do
      if let some childId := entry.bodyId then
        let some child := document.bodies[childId]? | throw s!"{path}.promoted_bodies: body is absent"
        unless child.instanceId == value.entryInstance do
          throw s!"{path}.promoted_bodies: instance identity mismatch"
  if let some selected := document.selectedScope then
    for (root, index) in selected.roots.toList.zipIdx do
      checkId b.definitions root.definitionId s!"$.selected_scope.roots[{index}].def_id" "definition"
  for target in document.sourceCastTargets do
    match target with
    | .functionPointer input instanceId =>
      checkId b.types input "$.source_cast_targets" "type"
      if let some id := instanceId then checkId b.instances id "$.source_cast_targets" "instance"
    | .closureOnce input instanceId =>
      checkId b.types input "$.source_cast_targets" "type"
      checkId b.instances instanceId "$.source_cast_targets" "instance"
  catalogs b document.queries
  validateExtraReferences document.types document.instances
  for node in document.instances do
    if let some ty := node.virtualIdentity then
      checkId b.types ty s!"$.instances[{node.id}].virtual_identity.function_type" "type"
    if let some id := node.fallbackInstance then checkId b.instances id s!"$.instances[{node.id}].fallback_instance" "instance"
  validateRequiredExecution document

end Miri.Input

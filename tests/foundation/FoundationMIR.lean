import Miri.Frontend.FoundationMIR

open Lean Miri Miri.Frontend.Foundation

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected foundation identity JSON")
  let source ← IO.FS.readFile path
  let check : Except String Unit := do
    let d ← Json.parse source >>= decode
    let some body := d.bodies[0]? | throw "missing body"
    let definition ← body.getObjValAs? Nat "definition"
    let prepared ← prepareItem d definition #[.type (.primitive "uint" "u8")]
    let candidate ← lowerPreparedMIR prepared
    let some block := candidate.body.basicBlocks[0]? | throw "missing lowered block"
    let some statement := block.statements[0]? | throw "missing assignment"
    match statement.kind with
    | .Assign destination (.Use (.Copy source) .Yes) =>
      unless destination.localId == 0 && source.localId == 1 do throw "wrong locals"
    | _ => throw "identity operand/retag changed"
    unless block.terminator.kind == .Return do throw "return changed"
    unless candidate.sourceLocations.size == block.statements.size + 1 do
      throw "source locations lost"
    let originalBlocks ← prepared.item.source.getObjValAs? (Array Json) "blocks"
    let some originalBlock := originalBlocks[0]? | throw "missing source block"
    let originalStatements ← originalBlock.getObjValAs? (Array Json) "statements"
    let some originalStatement := originalStatements[0]? | throw "missing source assignment"
    let originalValue ← originalStatement.getObjVal? "value"
    let originalOperand ← originalValue.getObjVal? "operand"
    let moveValue := (originalValue.setObjVal! "operand" (originalOperand.setObjVal! "kind" (toJson "move"))).setObjVal! "retag" (toJson false)
    let moveBlock := originalBlock.setObjVal! "statements" (toJson #[originalStatement.setObjVal! "value" moveValue])
    let moved := { prepared with item := { prepared.item with
      source := prepared.item.source.setObjVal! "blocks" (toJson #[moveBlock]) } }
    let moveCandidate ← lowerPreparedMIR moved
    let some moveBlock := moveCandidate.body.basicBlocks[0]? | throw "missing move block"
    let some moveStatement := moveBlock.statements[0]? | throw "missing move statement"
    match moveStatement.kind with
    | .Assign _ (.Use (.Move _) .No) => pure ()
    | _ => throw "Move/No retag changed"
    let rejectedBlock := originalBlock.setObjVal! "terminator" (Json.mkObj [("kind", toJson "unreachable")])
    let rejected := { prepared with item := { prepared.item with
      source := prepared.item.source.setObjVal! "blocks" (toJson #[rejectedBlock]) } }
    match lowerPreparedMIR rejected with
    | .error _ => pure ()
    | .ok _ => throw "unsupported terminator accepted"
  match check with
  | .error e => throw (IO.userError e)
  | .ok _ => IO.println "foundation MIR syntax: copy/move, retag, return, source and rejection checks passed"

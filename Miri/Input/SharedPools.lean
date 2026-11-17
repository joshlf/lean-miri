import Miri.Input.DecoderValues
import Miri.Input.DecodeMIR

namespace Miri.Input
open JsonReader DecoderValues

/-- Wire-only sharing. Semantic IDs continue to index the expanded tables, and
body-local effects of shared statements are checked separately at every use. -/
structure SharedPools where
  mir : DecodeMIR.MIRParser.SharedPools

private structure Fields where
  initializationRanges : Option (Array (Array InitRange)) := none
  relocations : Option (Array (Array Relocation)) := none
  sources : Option (Array SourceInfo) := none
  statements : Option String := none

/-- Retain only the statement pool's source until the independent allocation
pools are known. No generic JSON tree is constructed. -/
private def captureValue : Parser String := fun start =>
  match skipValue start with
  | .error stop error => .error stop error
  | .success stop _ => .success stop (String.Pos.Raw.extract start.1 start.2.offset stop.2.offset)

private def parsePools : Parser SharedPools := do
  let fields ← object ({} : Fields) fun fields key => do
    match key with
    | "initialization_ranges" => return {fields with initializationRanges := some (← arrayIndexed fun i => array (parseInitRange s!"$.initialization_ranges[{i}]"))}
    | "relocations" => return {fields with relocations := some (← arrayIndexed fun i => array (parseRelocation s!"$.relocations[{i}]"))}
    | "source_infos" => return {fields with sources := some (← arrayIndexed fun i => parseSourceInfo s!"$.source_infos[{i}]")}
    | "statement_kinds" => return {fields with statements := some (← captureValue)}
    | _ => skipValue; pure fields
  let mir : DecodeMIR.MIRParser.SharedPools := {
    initializationRanges := ← required fields.initializationRanges "initialization_ranges"
    relocations := ← required fields.relocations "relocations"
    sources := ← required fields.sources "source_infos" }
  let statements ← liftExcept (JsonReader.run (array (DecodeMIR.parseSharedStatement mir))
    (← required fields.statements "statement_kinds") |>.mapError (fun error => s!"$.statement_kinds: {error}"))
  pure {
    mir := {mir with statements} }

/-- Inspect shared tables before the main streaming parse, allowing every root
field ordering, including payloads occurring after references. -/
def readSharedPools : Parser SharedPools := fun start =>
  match parsePools start with
  | .error stop error => .error stop error
  | .success _ value => .success start value

end Miri.Input

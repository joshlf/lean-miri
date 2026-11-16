import Miri.Input.TableCore

open Miri.Input

private def declaration : String := r#"{"normalized_type":0,"closure_upvars":[],"variant_discriminants":[],"simd":null,"coroutine":null,"special_float":null,"is_x87_f80":false,"scalable_vectors":null,"variances":[],"has_destructor":false,"is_dyn_metadata":false,"type_id_hash":null,"is_unsafe_cell":false,"is_unsafe_pinned":false,"is_manually_drop":false,"is_maybe_uninit":false,"is_phantom_data":false,"is_box":false,"is_global_allocator":false,"is_c_void":false,"is_maybe_dangling":false,"nonnull_optimization_guaranteed":false,"definition":null,"item_name":null,"cfi_encoding":null,"capture_names":null}"#

private def decode (source : String) :=
  JsonReader.run DecoderValues.parseTypeNode
    ("{\"type_id\":0,\"display\":\"bool\",\"shape\":{\"kind\":\"bool\"},\"source_layout\":" ++ source ++ "}")

def main : IO Unit := do
  let .ok node := decode declaration | throw (IO.userError "complete source declaration was rejected")
  unless node.sourceLayout.normalizedType == 0 && node.shapeKind == .bool do
    throw (IO.userError "typed source declaration changed identity")
  for invalid in #[
      declaration.replace "\"normalized_type\":0," "",
      declaration.replace "\"is_box\":false" "\"is_box\":0",
      declaration.replace "\"normalized_type\":0" "\"normalized_type\":0,\"normalized_type\":0",
      declaration.replace "\"variances\":[]" "\"variances\":[{\"kind\":\"unknown\"}]"] do
    if (decode invalid).isOk then throw (IO.userError "invalid source declaration was accepted")
  let old := r#"{"type_id":0,"display":"bool","shape":{"kind":"bool"},"layout":0,"layout_query_input_type":null}"#
  if (JsonReader.run DecoderValues.parseTypeNode old).isOk then
    throw (IO.userError "query-result-only type record was accepted")
  IO.println "Source type input boundary checks passed"

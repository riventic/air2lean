import Air2Lean.Diagnose

/-! Synthetic diagnostic routing regressions. ROOT runs this with pinned Lean;
these checks are not compiler-generated fixture or semantics qualification. -/
open Lean Air2Lean Air2Lean.Diagnostics

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def obj (fields : List (String × Json)) : Json := Json.mkObj fields
private def num (n : Nat) : Json := toJson n
private def instruction (tag : String) (typed : Bool := true)
    (marked : Bool := true) : Json :=
  obj ([("id", num 42), ("tag", .str tag), ("unsupported", .bool marked)] ++
    if typed then [("ty", num 0)] else [])
private def file (body : Array Json) (version : String := "0.16.0") : Json :=
  obj [("schema", num 11), ("zig_version", .str version), ("name", .str "routing"),
    ("types", .arr #[obj [("k", .str "void")]]), ("params", .arr #[]),
    ("ret", num 0), ("body", .arr body)]
private def process (j : Json) : Except String Func := do
  normalizeCanonical (← Raw.parseFunc j)
private def has (s fragment : String) : Bool := decide ((s.splitOn fragment).length > 1)
private def rejectedWith (j : Json) (fragment : String) : IO Unit :=
  match process j with
  | .error e => require (has e fragment) s!"wrong rejection: {e}"
  | .ok _ => throw (IO.userError "accepted a rejected compiler/runtime tag")

def main : IO Unit := do
  let families := #[
    ("inferred_alloc", "unresolved inferred allocation", "0.16.0"),
    ("inferred_alloc_comptime", "unresolved inferred allocation", "0.16.0"),
    ("legalize_vec_store_elem", "compiler legalization", "0.16.0"),
    ("legalize_vec_elem_val", "compiler legalization", "0.16.0"),
    ("legalize_compiler_rt_call", "compiler legalization", "0.16.0"),
    ("runtime_nav_ptr", "identity and lifetime", "0.16.0"),
    ("err_return_trace", "mutable error-return-trace", "0.16.0"),
    ("set_err_return_trace", "mutable error-return-trace", "0.16.0"),
    ("save_err_return_trace_index", "mutable error-return-trace", "0.16.0"),
    ("vector_store_elem", "vector-element memory writes", "0.15.2"),
    ("cmp_lt_errors_len", "finalized compiler error universe", "0.15.2"),
    ("cmp_lte_errors_len", "finalized compiler error universe", "0.16.0")]
  for (tag, reason, version) in families do
    for marked in [false, true] do
      let j := file #[instruction tag true marked] version
      rejectedWith j reason
      rejectedWith j s!"routing: inst 42: tag '{tag}'"
      -- Recursive normalization preserves the nested instruction context.
      let nested := file #[obj [("id", num 7), ("tag", .str "block"),
        ("ty", num 0), ("body", .arr #[instruction tag true marked])]] version
      rejectedWith nested s!"routing: inst 42: tag '{tag}'"
    let (_, log) := inspect "runtime-tags.json" (file #[instruction tag] version).compress {}
    require (log.items.any (fun d => d.code == .exporterUnsupported &&
      d.anchor.instruction == some 42 && has d.message reason))
      "structured exporter marker must retain the shared reason and exported id"
  for tag in ["inferred_alloc", "inferred_alloc_comptime"] do
    for version in ["0.14.1", "0.15.2", "0.16.0"] do
      rejectedWith (file #[instruction tag false] version) "unresolved inferred allocation"
  for tag in ["unknown_plain", "runtime_nav_ptr", "err_return_trace"] do
    rejectedWith (file #[instruction tag false false]) "routing: inst 42: missing 'ty'"
  rejectedWith (file #[instruction "unknown_plain" true false]) "unknown AIR tag 'unknown_plain'"
  rejectedWith (file #[instruction "unknown_plain"]) "unsupported by the exporter"
  rejectedWith (file #[instruction "add" true false]) "needs 2 args"
  rejectedWith (file #[instruction "add_optimized"]) "optimized float mode"
  rejectedWith (file #[instruction "legalize_vec_elem_val"] "0.99.0") "unsupported zig_version"
  let malformed := file #[obj [("id", num 42), ("tag", .str "runtime_nav_ptr"),
    ("ty", num 0), ("args", .bool false)]]
  rejectedWith malformed "'args' must be an array"
  -- Existing admitted normalizer control, without claiming whole-function validation.
  let accepted := file #[obj [("id", num 0), ("tag", .str "dbg_empty_stmt"), ("ty", num 0)]]
  require (process accepted).toOption.isSome "ordinary admitted operation must remain admitted"

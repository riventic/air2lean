import Lean.Data.Json.Parser
import Std.Data.HashSet

/-! AIR JSON uses Lean's scalar parsers, while object parsing rejects decoded duplicate keys.
Bounds apply before arbitrary-precision number conversion or recursive container descent. -/
namespace Air2Lean.StrictJson
open Lean Std.Internal.Parsec Std.Internal.Parsec.String

/-- Maximum UTF-8 input bytes per AIR file. -/
def maxBytes : Nat := 64 * 1024 * 1024
/-- Maximum nested JSON containers; root scalars have depth zero. -/
def maxDepth : Nat := 128

private partial def numberToken (acc : String := "") : Parser String := do
  if ← isEof then return acc
  let c ← peek!
  if c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E' || ('0' ≤ c && c ≤ '9') then
    if acc.length ≥ 1024 then fail "JSON number exceeds 1024 characters"
    skip
    numberToken (acc.push c)
  else return acc

private def number : Parser Json := do
  let token ← numberToken
  let parts := (token.toLower.splitOn "e")
  match parts with
  | [_] => pure ()
  | [_, exponent] =>
    let exponent := if exponent.startsWith "+" then (exponent.drop 1).toString else exponent
    let some n := exponent.toInt? | fail "invalid JSON exponent"
    if n.natAbs > 4096 then fail "JSON exponent exceeds magnitude 4096"
  | _ => fail "invalid JSON exponent"
  match Parser.run (Lean.Json.Parser.num <* eof) token with
  | .error e => fail e
  | .ok n => return .num n

mutual
private partial def value (depth : Nat) : Parser Json := do
  let c ← peek!
  let result ←
    if c == '{' then
      if depth ≥ maxDepth then fail s!"JSON nesting exceeds {maxDepth} containers"
      skip; ws
      if (← peek!) == '}' then
        skip
        pure (Json.mkObj [])
      else object depth {} []
    else if c == '[' then
      if depth ≥ maxDepth then fail s!"JSON nesting exceeds {maxDepth} containers"
      skip; ws
      if (← peek!) == ']' then
        skip
        pure (.arr #[])
      else array depth #[]
    else if c == '"' then
      skip
      Json.str <$> Lean.Json.Parser.str
    else if c == 't' then skipString "true" *> pure (.bool true)
    else if c == 'f' then skipString "false" *> pure (.bool false)
    else if c == 'n' then skipString "null" *> pure .null
    else if c == '-' || ('0' ≤ c && c ≤ '9') then number
    else fail "unexpected JSON input"
  ws
  return result

private partial def object (depth : Nat) (seen : Std.HashSet String)
    (fields : List (String × Json)) : Parser Json := do
  skipString "\""
  let key ← Lean.Json.Parser.str
  if seen.contains key then fail s!"duplicate JSON object key {repr key}"
  ws; skipString ":"; ws
  let v ← value (depth + 1)
  let c ← any
  if c == '}' then return Json.mkObj ((key, v) :: fields)
  else if c == ',' then
    ws
    object depth (seen.insert key) ((key, v) :: fields)
  else fail "expected ',' or '}' in JSON object"

private partial def array (depth : Nat) (items : Array Json) : Parser Json := do
  let v ← value (depth + 1)
  let c ← any
  if c == ']' then return .arr (items.push v)
  else if c == ',' then
    ws
    array depth (items.push v)
  else fail "expected ',' or ']' in JSON array"
end

/-- Decode without discarding any repeated object key, including escaped spelling aliases. -/
def parse (contents : String) : Except String Json := do
  if contents.utf8ByteSize > maxBytes then
    throw s!"AIR JSON exceeds {maxBytes} UTF-8 bytes"
  Parser.run (ws *> value 0 <* eof) contents
end Air2Lean.StrictJson

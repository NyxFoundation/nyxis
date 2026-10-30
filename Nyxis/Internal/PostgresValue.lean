import Nyxis.Db
import Lean.Data.Json

/-! The internal JSONB cell format for application Cedar values. This is neither SQL execution nor authorization. Stores
scalars (the primitives `Bool` / `Long` / `String` / entity references, and the extension values `decimal` / `datetime`
/ `duration`), sets of scalars, and records with scalar attributes. Nested sets and records (sets of sets, records
containing sets) and `ipaddr` are rejected. The type tag keeps strings distinct from entity references, and integers
distinct from extension values. PostgreSQL JSONB cannot store NUL, so it is rejected. Errors never include the input.

Format (JSON array): `["bool", b]` / `["int", "decimal digits"]` / `["string", s]` /
`["entity", [namespace…], type name, ID]` / `["decimal", "decimal digits of the internal representation"]` /
`["datetime", "milliseconds since the epoch"]` / `["duration", "milliseconds"]` / `["set", [scalar…]]` /
`["record", [[attribute name, scalar]…]]`. All integer kinds use canonical signed 64-bit decimal notation.
-/
namespace Nyxis.Internal.PostgresValue
open Cedar.Spec Lean

private def invalid : Except String α := .error "Unsupported or invalid PostgreSQL cell"

private def text (s : String) : Except String Json :=
  if s.contains '\x00' then invalid else .ok (.str s)

/-- Canonical decimal notation of a signed 64-bit integer. -/
private def int64Text (i : Int64) : Json := .str (toString i.toInt)

/-- The elements of the tagged array for a scalar value (primitives and extension values). Sets, records and `ipaddr`
are rejected. -/
def scalarFields (value : Value) : Except String (Array Json) :=
  match value with
  | .prim (.bool b) => pure #[.str "bool", .bool b]
  | .prim (.int i) => pure #[.str "int", int64Text i]
  | .prim (.string s) => do pure #[.str "string", ← text s]
  | .prim (.entityUID uid) => do
    let path ← uid.ty.path.toArray.mapM text
    pure #[.str "entity", .arr path, ← text uid.ty.id, ← text uid.eid]
  | .ext (.decimal d) => pure #[.str "decimal", int64Text d]
  | .ext (.datetime dt) => pure #[.str "datetime", int64Text dt.val]
  | .ext (.duration du) => pure #[.str "duration", int64Text du.val]
  | _ => invalid

/-- The JSON of a scalar value (a set element or a record attribute value). -/
def scalar (value : Value) : Except String Json := do
  return .arr (← scalarFields value)

/-- The elements of the tagged array for a whole cell. Elements of sets and records are limited to scalars. -/
def fields (value : Value) : Except String (Array Json) :=
  match value with
  | .set s => do pure #[.str "set", .arr (← s.toList.toArray.mapM scalar)]
  | .record m => do
    let pairs ← m.toList.toArray.mapM fun (k, v) => do pure (Json.arr #[← text k, ← scalar v])
    pure #[.str "record", .arr pairs]
  | v => scalarFields v

def encode (value : Value) : Except String String := do
  return (Json.arr (← fields value)).compress

private def string (j : Json) : Except String String := do
  match j with
  | .str s => if s.contains '\x00' then invalid else pure s
  | _ => invalid

/-- From a string in canonical decimal notation to a signed 64-bit integer. -/
private def int64 (j : Json) : Except String Int64 :=
  match j with
  | .str digits =>
    match digits.toInt? with
    | some i =>
      if i < -9223372036854775808 || i > 9223372036854775807 || toString i != digits then
        invalid
      else .ok (Int64.ofInt i)
    | none => invalid
  | _ => invalid

/-- Decodes the tagged array of a scalar. -/
def decodeScalar (json : Json) : Except String Value :=
  match json with
  | .arr fields =>
    match fields.toList with
    | [.str "bool", .bool b] => pure (.prim (.bool b))
    | [.str "int", j] => do return .prim (.int (← int64 j))
    | [.str "string", j] => do return .prim (.string (← string j))
    | [.str "entity", .arr path, name, eid] => do
      let segments ← path.toList.mapM string
      return .prim (.entityUID ⟨⟨← string name, segments⟩, ← string eid⟩)
    | [.str "decimal", j] => do return .ext (.decimal (← int64 j))
    | [.str "datetime", j] => do return .ext (.datetime ⟨← int64 j⟩)
    | [.str "duration", j] => do return .ext (.duration ⟨← int64 j⟩)
    | _ => invalid
  | _ => invalid

/-- A record attribute `[attribute name, scalar]`. -/
private def pair (j : Json) : Except String (Attr × Value) :=
  match j with
  | .arr fields =>
    match fields.toList with
    | [kj, vj] => do return (← string kj, ← decodeScalar vj)
    | _ => invalid
  | _ => invalid

def decode (stored : String) : Except String Value := do
  let json ← (Json.parse stored).mapError (fun _ => "Invalid PostgreSQL cell JSON")
  match json with
  | .arr fields =>
    match fields.toList with
    | [.str "set", .arr elems] => do
      let values ← elems.toList.mapM decodeScalar
      pure (.set (Cedar.Data.Set.make values))
    | [.str "record", .arr pairs] => do
      let kvs ← pairs.toList.mapM pair
      if (kvs.map Prod.fst).eraseDups != kvs.map Prod.fst then invalid
      else pure (.record (Cedar.Data.Map.make kvs))
    | _ => decodeScalar (.arr fields)
  | _ => invalid

/-- Canonical decimal notation within the signed 64-bit range. -/
inductive DecodedInt64 : Json → Int64 → Prop where
  | mk (digits : String) (i : Int)
      (parsed : digits.toInt? = some i)
      (lower : -9223372036854775808 ≤ i) (upper : i ≤ 9223372036854775807)
      (canonical : toString i = digits) :
      DecodedInt64 (.str digits) (Int64.ofInt i)

/-- The parsed JSON of a scalar has exactly one corresponding tag and preserves its value. The decimal notation of
integers and extension values is canonical and within the signed 64-bit range, and each string part contains no NUL.
This relation assumes nothing about external SQL storage. -/
inductive DecodedScalar : Json → Value → Prop where
  | bool (b : Bool) (fields : Array Json)
      (shape : fields.toList = [.str "bool", .bool b]) :
      DecodedScalar (.arr fields) (.prim (.bool b))
  | int (j : Json) (i : Int64) (fields : Array Json)
      (shape : fields.toList = [.str "int", j]) (value : DecodedInt64 j i) :
      DecodedScalar (.arr fields) (.prim (.int i))
  | string (s : String) (fields : Array Json)
      (shape : fields.toList = [.str "string", .str s])
      (noNul : s.contains '\x00' = false) :
      DecodedScalar (.arr fields) (.prim (.string s))
  | entity (path : Array Json) (segments : List String) (name eid : String)
      (fields : Array Json)
      (shape : fields.toList = [.str "entity", .arr path, .str name, .str eid])
      (parts : List.Forall₂ (fun j s => j = .str s ∧ s.contains '\x00' = false)
        path.toList segments)
      (nameNoNul : name.contains '\x00' = false) (eidNoNul : eid.contains '\x00' = false) :
      DecodedScalar (.arr fields) (.prim (.entityUID ⟨⟨name, segments⟩, eid⟩))
  | decimal (j : Json) (d : Int64) (fields : Array Json)
      (shape : fields.toList = [.str "decimal", j]) (value : DecodedInt64 j d) :
      DecodedScalar (.arr fields) (.ext (.decimal d))
  | datetime (j : Json) (ms : Int64) (fields : Array Json)
      (shape : fields.toList = [.str "datetime", j]) (value : DecodedInt64 j ms) :
      DecodedScalar (.arr fields) (.ext (.datetime ⟨ms⟩))
  | duration (j : Json) (ms : Int64) (fields : Array Json)
      (shape : fields.toList = [.str "duration", j]) (value : DecodedInt64 j ms) :
      DecodedScalar (.arr fields) (.ext (.duration ⟨ms⟩))

/-- The relation between the JSON of a record attribute `[attribute name, scalar]` and the decoded (attribute name,
value). -/
def DecodedPair (j : Json) (kv : Attr × Value) : Prop :=
  ∃ fields vj, j = .arr fields ∧ fields.toList = [.str kv.1, vj] ∧
    kv.1.contains '\x00' = false ∧ DecodedScalar vj kv.2

/-- The parsed JSON is either a scalar, a set constructed with `Set.make` from a list of scalars, or a record
constructed with `Map.make` from a list of distinct attribute names and scalars. -/
inductive Decoded : Json → Value → Prop where
  | scalar (json : Json) (value : Value) (h : DecodedScalar json value) : Decoded json value
  | set (elems : Array Json) (values : List Value) (fields : Array Json)
      (shape : fields.toList = [.str "set", .arr elems])
      (parts : List.Forall₂ DecodedScalar elems.toList values) :
      Decoded (.arr fields) (.set (Cedar.Data.Set.make values))
  | record (pairs : Array Json) (kvs : List (Attr × Value)) (fields : Array Json)
      (shape : fields.toList = [.str "record", .arr pairs])
      (parts : List.Forall₂ DecodedPair pairs.toList kvs)
      (unique : (kvs.map Prod.fst).eraseDups = kvs.map Prod.fst) :
      Decoded (.arr fields) (.record (Cedar.Data.Map.make kvs))

private theorem string_success (j : Json) (s : String) (h : string j = .ok s) :
    j = .str s ∧ s.contains '\x00' = false := by
  unfold string at h
  split at h
  · split at h
    · cases h
    · rename_i hn
      cases h
      exact ⟨rfl, by simpa using hn⟩
  · cases h

private theorem mapM_success {α β : Type} (f : α → Except String β) (R : α → β → Prop)
    (hf : ∀ a b, f a = .ok b → R a b) (xs : List α) (ys : List β)
    (h : xs.mapM f = .ok ys) : List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
    change Except.ok [] = Except.ok ys at h
    cases h
    exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x with
    | error e => simp [hx, bind, Except.bind] at h
    | ok y =>
      cases ht : xs.mapM f with
      | error e => simp [hx, ht, bind, Except.bind] at h
      | ok tail =>
        simp only [hx, ht] at h
        change Except.ok (y :: tail) = Except.ok ys at h
        cases h
        exact .cons (hf x y hx) (ih tail ht)

private theorem int64_success (j : Json) (v : Int64) (h : int64 j = .ok v) : DecodedInt64 j v := by
  unfold int64 at h
  split at h
  · rename_i digits
    split at h
    · rename_i i hi
      split at h
      · cases h
      · rename_i bounds
        cases h
        simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, not_or] at bounds
        exact .mk digits i hi (by omega) (by omega) (by simpa using bounds.2)
    · cases h
  · cases h

/-- When the real decodeScalar succeeds, it returns the scalar value of the corresponding tag. Integers and extension
values are in canonical decimal notation within the Int64 range, and strings and each entity namespace element/type
name/ID contain no NUL. -/
theorem decodeScalar_success (json : Json) (value : Value) (h : decodeScalar json = .ok value) :
    DecodedScalar json value := by
  unfold decodeScalar at h
  split at h
  · rename_i fields
    split at h
    · rename_i b hs
      cases h
      exact .bool b fields hs
    · rename_i j hs
      cases hi : int64 j with
      | error e => simp [hi, bind, Except.bind] at h
      | ok i =>
        simp only [hi] at h
        cases h
        exact .int j i fields hs (int64_success j i hi)
    · rename_i j hs
      cases hj : string j with
      | error e => simp [hj, bind, Except.bind] at h
      | ok s =>
        simp only [hj] at h
        cases h
        obtain ⟨rfl, hn⟩ := string_success j s hj
        exact .string s fields hs hn
    · rename_i path name eid hs
      cases ht : path.toList.mapM string with
      | error e => simp [ht, bind, Except.bind] at h
      | ok segments =>
        simp only [ht] at h
        cases hn : string name with
        | error e => simp [hn, bind, Except.bind] at h
        | ok n =>
          simp only [hn] at h
          cases he : string eid with
          | error e => simp [he, bind, Except.bind] at h
          | ok e =>
            simp only [he] at h
            cases h
            obtain ⟨rfl, hnn⟩ := string_success name n hn
            obtain ⟨rfl, hen⟩ := string_success eid e he
            exact .entity path segments n e fields hs
              (mapM_success string _ string_success _ _ ht) hnn hen
    · rename_i j hs
      cases hi : int64 j with
      | error e => simp [hi, bind, Except.bind] at h
      | ok d =>
        simp only [hi] at h
        cases h
        exact .decimal j d fields hs (int64_success j d hi)
    · rename_i j hs
      cases hi : int64 j with
      | error e => simp [hi, bind, Except.bind] at h
      | ok ms =>
        simp only [hi] at h
        cases h
        exact .datetime j ms fields hs (int64_success j ms hi)
    · rename_i j hs
      cases hi : int64 j with
      | error e => simp [hi, bind, Except.bind] at h
      | ok ms =>
        simp only [hi] at h
        cases h
        exact .duration j ms fields hs (int64_success j ms hi)
    · cases h
  · cases h

private theorem pair_success (j : Json) (kv : Attr × Value) (h : pair j = .ok kv) :
    DecodedPair j kv := by
  unfold pair at h
  split at h
  · rename_i fields
    split at h
    · rename_i kj vj hs
      cases hk : string kj with
      | error e => simp [hk, bind, Except.bind] at h
      | ok k =>
        simp only [hk] at h
        cases hv : decodeScalar vj with
        | error e => simp [hv, bind, Except.bind] at h
        | ok v =>
          simp only [hv] at h
          cases h
          obtain ⟨rfl, hn⟩ := string_success kj k hk
          exact ⟨fields, vj, rfl, hs, hn, decodeScalar_success vj v hv⟩
    · cases h
  · cases h

/-- When the real decode succeeds, JSON parsing also succeeds, and it returns the per-tag value for a scalar, Set.make
over a list of scalars for a set, and Map.make over distinct attribute names and a list of scalars for a record.
Integers and extension values are in canonical decimal notation within the Int64 range, and strings, each part of an
entity, and attribute names contain no NUL. The JSON parser internals and the semantics of the external DB's actual
state are not included. -/
theorem decode_success (stored : String) (value : Value) (h : decode stored = .ok value) :
    ∃ json, Json.parse stored = .ok json ∧ Decoded json value := by
  unfold decode at h
  cases hp : Json.parse stored with
  | error e => simp [hp, Except.mapError, bind, Except.bind] at h
  | ok json =>
    simp only [hp, Except.mapError, bind, Except.bind] at h
    refine ⟨json, rfl, ?_⟩
    split at h
    · rename_i fields
      split at h
      · rename_i elems hs
        cases hm : elems.toList.mapM decodeScalar with
        | error e => simp [hm] at h
        | ok values =>
          simp only [hm] at h
          cases h
          exact .set elems values fields hs (mapM_success decodeScalar _ decodeScalar_success _ _ hm)
      · rename_i pairs hs
        cases hm : pairs.toList.mapM pair with
        | error e => simp [hm] at h
        | ok kvs =>
          simp only [hm] at h
          split at h
          · cases h
          · rename_i unique
            cases h
            exact .record pairs kvs fields hs (mapM_success pair _ pair_success _ _ hm)
              (by simpa using unique)
      · exact .scalar _ _ (decodeScalar_success _ _ h)
    · cases h

/-- Converting a Cedar integer in the int-tag decoding relation back to a mathematical integer gives the integer denoted
by the input's canonical decimal notation. Thanks to the range check, the Int64 conversion does not change the value. -/
theorem Decoded.int_value (json : Json) (value : Int64)
    (h : Decoded json (.prim (.int value))) :
    ∃ fields digits, json = .arr fields ∧
      fields.toList = [.str "int", .str digits] ∧
      digits.toInt? = some value.toInt ∧ toString value.toInt = digits := by
  cases h with
  | scalar _ _ hs =>
    cases hs with
    | int j i fields shape hv =>
      cases hv with
      | mk digits i parsed lower upper canonical =>
        have preserved : (Int64.ofInt i).toInt = i :=
          Int64.toInt_ofInt_of_le (by change -9223372036854775808 ≤ i; exact lower)
            (by change i < 9223372036854775808; omega)
        exact ⟨fields, digits, rfl, shape, by rw [preserved]; exact parsed,
          by rw [preserved]; exact canonical⟩

/-- If the real decode returns a Cedar integer, JSON parsing returns the int tag and a canonical decimal string, and the
mathematical integer of that string equals toInt of the returned Cedar integer. Nothing is claimed about the JSON parser
internals or agreement with the external DB. -/
theorem decode_int_success (stored : String) (value : Int64)
    (h : decode stored = .ok (.prim (.int value))) :
    ∃ fields digits, Json.parse stored = .ok (.arr fields) ∧
      fields.toList = [.str "int", .str digits] ∧
      digits.toInt? = some value.toInt ∧ toString value.toInt = digits := by
  obtain ⟨json, parsed, related⟩ := decode_success stored _ h
  obtain ⟨fields, digits, rfl, shape, integer, canonical⟩ := Decoded.int_value json value related
  exact ⟨fields, digits, parsed, shape, integer, canonical⟩

end Nyxis.Internal.PostgresValue

import Nyxis.Db
import Lean.Data.Json

/-! アプリケーションの Cedar の値のための内部の JSONB セル形式。SQL の実行でも認可でもない。
スカラー(プリミティブ `Bool` / `Long` / `String` / 実体参照と、拡張値 `decimal` / `datetime` / `duration`)、
スカラーの集合、スカラーを属性に持つレコードを保存する。集合やレコードの入れ子(集合の集合、集合を持つ
レコード)と `ipaddr` は拒む。型のタグが文字列と実体参照、整数と拡張値を区別して保つ。
PostgreSQL の JSONB は NUL を保存できないので拒む。エラーに入力を含めない。

形式(JSON 配列): `["bool", b]` / `["int", "十進"]` / `["string", s]` / `["entity", [名前空間…], 型名, ID]` /
`["decimal", "内部表現の十進"]` / `["datetime", "エポックからのミリ秒"]` / `["duration", "ミリ秒"]` /
`["set", [スカラー…]]` / `["record", [[属性名, スカラー]…]]`。整数系はすべて符号つき 64 ビットの正規十進表記。
-/
namespace Nyxis.Internal.PostgresValue
open Cedar.Spec Lean

private def invalid : Except String α := .error "Unsupported or invalid PostgreSQL cell"

private def text (s : String) : Except String Json :=
  if s.contains '\x00' then invalid else .ok (.str s)

/-- 符号つき 64 ビット整数の正規十進表記。 -/
private def int64Text (i : Int64) : Json := .str (toString i.toInt)

/-- スカラー値(プリミティブと拡張値)のタグつき配列の要素。集合・レコード・`ipaddr` は拒む。 -/
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

/-- スカラー値の JSON(集合の要素・レコードの属性値)。 -/
def scalar (value : Value) : Except String Json := do
  return .arr (← scalarFields value)

/-- セル全体のタグつき配列の要素。集合とレコードの要素はスカラーに限る。 -/
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

/-- 正規十進表記の文字列から符号つき 64 ビット整数へ。 -/
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

/-- スカラーのタグつき配列を復号する。 -/
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

/-- レコードの属性 `[属性名, スカラー]`。 -/
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

/-- 符号つき 64 ビットの範囲内の正規十進表記。 -/
inductive DecodedInt64 : Json → Int64 → Prop where
  | mk (digits : String) (i : Int)
      (parsed : digits.toInt? = some i)
      (lower : -9223372036854775808 ≤ i) (upper : i ≤ 9223372036854775807)
      (canonical : toString i = digits) :
      DecodedInt64 (.str digits) (Int64.ofInt i)

/-- 解析したスカラーの JSON は対応するタグをちょうど 1 つ持ち、その値を保つ。
整数・拡張値の十進表記は正規で符号つき 64 ビットの範囲内、文字列の各部分は NUL を含まない。
この関係は外部の SQL の保存について何も仮定しない。 -/
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

/-- レコードの属性の JSON `[属性名, スカラー]` と、復号した (属性名, 値) の関係。 -/
def DecodedPair (j : Json) (kv : Attr × Value) : Prop :=
  ∃ fields vj, j = .arr fields ∧ fields.toList = [.str kv.1, vj] ∧
    kv.1.contains '\x00' = false ∧ DecodedScalar vj kv.2

/-- 解析した JSON は、スカラーか、スカラーの列から `Set.make` で構成した集合か、
重複しない属性名とスカラーの列から `Map.make` で構成したレコードである。 -/
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

/-- 日本語: 実decodeScalarが成功すると、対応するタグのスカラー値を返す。整数と拡張値は
Int64範囲内の正規十進表記で、文字列・entityの名前空間各要素/型名/IDはNULを含まない。 -/
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

/-- 日本語: 実decodeが成功するとJSON解析も成功し、スカラーならタグ別の値、集合なら
スカラー列からのSet.make、レコードなら重複しない属性名とスカラー列からのMap.makeを返す。
整数・拡張値はInt64範囲内の正規十進表記で、文字列・entityの各部と属性名はNULを含まない。
JSON解析器内部や外部DB実状態の意味論は含まない。 -/
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

/-- 日本語: intタグの復号関係にあるCedar整数を数学的整数へ戻すと、
入力の正規十進表記が表す整数と一致する。範囲検査によりInt64変換で値は変わらない。 -/
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

/-- 日本語: 実decodeがCedar整数を返したなら、JSON解析はintタグと正規十進文字列を
返し、その文字列の数学的整数は返却Cedar整数のtoIntと等しい。
JSON解析器の内部や外部DBとの一致は主張しない。 -/
theorem decode_int_success (stored : String) (value : Int64)
    (h : decode stored = .ok (.prim (.int value))) :
    ∃ fields digits, Json.parse stored = .ok (.arr fields) ∧
      fields.toList = [.str "int", .str digits] ∧
      digits.toInt? = some value.toInt ∧ toString value.toInt = digits := by
  obtain ⟨json, parsed, related⟩ := decode_success stored _ h
  obtain ⟨fields, digits, rfl, shape, integer, canonical⟩ := Decoded.int_value json value related
  exact ⟨fields, digits, parsed, shape, integer, canonical⟩

end Nyxis.Internal.PostgresValue

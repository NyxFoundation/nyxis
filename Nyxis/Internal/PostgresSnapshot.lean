import Nyxis.Internal.PostgresSql

/-! 内部の SELECT スナップショットの純粋な復号(A4。定理の外)。
SQL の NULL は属性の欠落を意味し、Cedar の値にはならない。Store を返す前にスナップショット全体を
検証する。Map.make が重複した主キーを黙って潰してはならない。
呼び出し側はすべてのテーブルを同じ SERIALIZABLE トランザクションの中で読まなければならない。
このモジュールは SQL を実行せず、認可もせず、ハンドラにデータを返さない。
-/
namespace Nyxis.Internal.PostgresSnapshot
open Nyxis Db Cedar.Spec

/-- PostgresSql.selectTable のテキスト形式の結果。none は SQL の NULL。 -/
structure Result where
  columns : List String
  rows : List (List (Option String))
  deriving BEq, Repr

private def invalid : Except String α := .error "Invalid PostgreSQL snapshot"

private def attributes (columns : List Column) (values : List (Option String)) :
    Except String Row := do
  if columns.length != values.length then invalid else do
    let cells ← (columns.zip values).mapM fun (column, value) => do
      match value with
      | none => pure none
      | some stored => return some (column, ← PostgresValue.decode stored)
    return Cedar.Data.Map.make (cells.filterMap id)

/-- 写像を作る前に、SELECT の投影と各行を、重複も含めて検査する。 -/
def tableRows (schema : Authz.Schema) (table : Table) (result : Result) :
    Except String (List (EntityUID × Row)) := do
  -- SQL の配置の検証を再利用する(対応しないテーブルと識別子の衝突を含む)。
  let _ ← PostgresSql.selectTable schema table
  let some columns := (schema.tables.find? (fun entry => entry.1 == table)).map Prod.snd
    | invalid
  if result.columns != "_nyxis_id" :: columns then invalid else do
    let rows ← result.rows.mapM fun values => do
      let some key :: cells := values | invalid
      if key.contains '\x00' then invalid else do
        return ((⟨table, key⟩ : EntityUID), ← attributes columns cells)
    let keys := rows.map Prod.fst
    if keys.eraseDups != keys then invalid else pure rows

/-- スキーマの各テーブルにちょうど 1 つの結果を要求する。テーブルの欠落は空のテーブルではない。
結果の順序は問わない。重複・余分・対応しないテーブルは拒む。
-/
def restore (schema : Authz.Schema) (results : List (Table × Result)) : Except String Store := do
  let expected := schema.tables.map Prod.fst
  let actual := results.map Prod.fst
  if expected.eraseDups != expected || actual.eraseDups != actual ||
      expected.length != actual.length || !expected.all actual.contains then invalid else do
    let rows ← results.mapM fun (table, result) => tableRows schema table result
    return Cedar.Data.Map.make rows.flatten

private theorem mapM_success (f : α → Except String β) (xs : List α) (ys : List β)
    (h : xs.mapM f = .ok ys) : List.Forall₂ (fun x y => f x = .ok y) xs ys := by
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
        exact .cons hx (ih tail ht)

private theorem forall₂_length (rel : α → β → Prop) (xs : List α) (ys : List β)
    (h : List.Forall₂ rel xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem forall₂_imp {r s : α → β → Prop}
    (imp : ∀ x y, r x y → s x y) {xs : List α} {ys : List β}
    (h : List.Forall₂ r xs ys) : List.Forall₂ s xs ys := by
  induction h with
  | nil => exact .nil
  | cons head _ ih => exact .cons (imp _ _ head) ih

/-- 入力の各セルは、属性を省く(SQL の NULL)か、復号に成功するかのどちらか。 -/
def AttributeCell (input : Column × Option String) (output : Option (Column × Cedar.Spec.Value)) : Prop :=
  match input.2 with
  | none => output = none
  | some stored => ∃ value, PostgresValue.decode stored = .ok value ∧
      output = some (input.1, value)

private theorem attributes_success (columns : List Column) (values : List (Option String))
    (row : Row) (h : attributes columns values = .ok row) :
    columns.length = values.length ∧ ∃ cells,
      List.Forall₂ AttributeCell (columns.zip values) cells ∧
      row = Cedar.Data.Map.make (cells.filterMap id) := by
  simp only [attributes] at h
  split at h
  · cases h
  · rename_i hl
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i cells hm
      change Except.ok (Cedar.Data.Map.make (cells.filterMap id)) = Except.ok row at h
      cases h
      refine ⟨by simpa using hl, cells, ?_, rfl⟩
      have related := mapM_success _ _ _ hm
      apply forall₂_imp ?_ related
      intro input output hc
      rcases input with ⟨column, value⟩
      cases value with
      | none =>
        change Except.ok none = Except.ok output at hc
        cases hc
        rfl
      | some stored =>
        cases hd : PostgresValue.decode stored with
        | error e => simp [hd] at hc
        | ok value =>
          simp only [hd] at hc
          change Except.ok (some (column, value)) = Except.ok output at hc
          cases hc
          exact ⟨value, hd, rfl⟩

/-- 主キーがあり NUL を含まない。属性は Map.make までは入力順を保つ。
構成について述べるもので、Cedar の写像の検索の意味論は述べない。 -/
def DecodedRow (table : Table) (columns : List Column)
    (input : List (Option String)) (output : EntityUID × Row) : Prop :=
  ∃ key values cells, input = some key :: values ∧ key.contains '\x00' = false ∧
    columns.length = values.length ∧
    List.Forall₂ AttributeCell (columns.zip values) cells ∧
    output = ((⟨table, key⟩ : EntityUID), Cedar.Data.Map.make (cells.filterMap id))

private theorem decodeRow_success (table : Table) (columns : List Column)
    (input : List (Option String)) (output : EntityUID × Row)
    (h : (do
      let some key :: cells := input | invalid
      if key.contains '\x00' then invalid else do
        return ((⟨table, key⟩ : EntityUID), ← attributes columns cells)) =
          Except.ok output) : DecodedRow table columns input output := by
  cases input with
  | nil => cases h
  | cons head values =>
    cases head with
    | none => cases h
    | some key =>
      simp only at h
      split at h
      · cases h
      · rename_i hk
        cases ha : attributes columns values with
        | error e => simp [ha, bind, Except.bind] at h
        | ok row =>
          simp only [ha, bind, Except.bind] at h
          change Except.ok ((⟨table, key⟩ : EntityUID), row) = Except.ok output at h
          cases h
          obtain ⟨hl, cells, hc, hr⟩ := attributes_success columns values row ha
          exact ⟨key, values, cells, rfl, by simpa using hk, hl, hc, by rw [hr]⟩

/-- 日本語: 実tableRowsが成功すると、投影は主キーと宣言列に一致し、入力順の
各行は非NULLかつNULを含まない主キーを持つ。属性セル数は宣言列数と等しく、
NULLは属性欠落、非NULLは実decode成功の値となり、その順のMap.makeが返却行を構成する。
値デコーダ内部・Map検索・外部DB実状態の意味論は含まない。 -/
theorem tableRows_cells (schema : Authz.Schema) (table : Table) (result : Result)
    (rows : List (EntityUID × Row)) (h : tableRows schema table result = .ok rows) :
    ∃ columns,
      (schema.tables.find? (fun entry => entry.1 == table)).map Prod.snd = some columns ∧
      result.columns = "_nyxis_id" :: columns ∧
      List.Forall₂ (DecodedRow table columns) result.rows rows := by
  simp only [tableRows] at h
  cases hc : PostgresSql.selectTable schema table with
  | error e => simp [hc, bind, Except.bind] at h
  | ok command =>
    simp only [hc, bind, Except.bind] at h
    cases hf : (schema.tables.find? (fun entry => entry.1 == table)).map Prod.snd with
    | none => simp only [hf] at h; cases h
    | some columns =>
      simp only [hf] at h
      split at h
      · cases h
      · rename_i hp
        change (do
          let decoded ← result.rows.mapM _
          if (decoded.map Prod.fst).eraseDups != decoded.map Prod.fst then invalid
          else pure decoded) = Except.ok rows at h
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i decoded hm
          split at h
          · cases h
          · change Except.ok decoded = Except.ok rows at h
            cases h
            refine ⟨columns, rfl, by simpa using hp, ?_⟩
            exact forall₂_imp (fun _ _ hr => decodeRow_success table columns _ _ hr)
              (mapM_success _ _ _ hm)

/-- 日本語: 実tableRowsが成功したなら、SELECT生成とテーブル検索が成功し、
列の並びは主キーと宣言列に一致する。復号前後の行数は等しく、復号後の
主キーに重複はない。セル値の復号とMap検索の意味論、外部DBとの一致は含まない。 -/
theorem tableRows_success (schema : Authz.Schema) (table : Table) (result : Result)
    (rows : List (EntityUID × Row)) (h : tableRows schema table result = .ok rows) :
    ∃ command columns, PostgresSql.selectTable schema table = .ok command ∧
      (schema.tables.find? (fun entry => entry.1 == table)).map Prod.snd = some columns ∧
      result.columns = "_nyxis_id" :: columns ∧
      result.rows.length = rows.length ∧
      (rows.map Prod.fst).eraseDups = rows.map Prod.fst := by
  simp only [tableRows] at h
  cases hc : PostgresSql.selectTable schema table with
  | error e => simp [hc, bind, Except.bind] at h
  | ok command =>
    simp only [hc, bind, Except.bind] at h
    cases hf : (schema.tables.find? (fun entry => entry.1 == table)).map Prod.snd with
    | none => simp only [hf] at h; cases h
    | some columns =>
      simp only [hf] at h
      split at h
      · cases h
      · rename_i hp
        change (do
          let decoded ← result.rows.mapM _
          if (decoded.map Prod.fst).eraseDups != decoded.map Prod.fst then invalid
          else pure decoded) = Except.ok rows at h
        simp only [bind, Except.bind] at h
        split at h
        · cases h
        · rename_i decoded hm
          split at h
          · cases h
          · rename_i hd
            change Except.ok decoded = Except.ok rows at h
            cases h
            have hl : result.rows.length = rows.length :=
              forall₂_length _ _ _ (mapM_success _ _ _ hm)
            exact ⟨command, columns, rfl, rfl, by simpa using hp, hl, by simpa using hd⟩

/-- 日本語: 実restoreが成功したなら、スキーマと結果のテーブル名に重複はなく、
個数が等しく、全スキーマテーブルが結果に含まれる。入力順の各結果について
実tableRowsが成功し、その復号行を同じ順序で連結したMapが返却Storeそのもの。
外部DB実状態やSQLの意味論、Mapの検索意味論は主張しない。 -/
theorem restore_success (schema : Authz.Schema) (results : List (Table × Result))
    (store : Store) (h : restore schema results = .ok store) :
    let expected := schema.tables.map Prod.fst
    let actual := results.map Prod.fst
    expected.eraseDups = expected ∧ actual.eraseDups = actual ∧
      expected.length = actual.length ∧
      (∀ table ∈ expected, table ∈ actual) ∧
      ∃ rows, List.Forall₂ (fun entry decoded =>
        tableRows schema entry.1 entry.2 = .ok decoded) results rows ∧
        store = Cedar.Data.Map.make rows.flatten := by
  simp only [restore] at h
  split at h
  · cases h
  · rename_i valid
    have hv : (schema.tables.map Prod.fst).eraseDups = schema.tables.map Prod.fst ∧
        (results.map Prod.fst).eraseDups = results.map Prod.fst ∧
        (schema.tables.map Prod.fst).length = (results.map Prod.fst).length ∧
        ∀ table ∈ schema.tables.map Prod.fst, table ∈ results.map Prod.fst := by
      simpa [Bool.or_eq_false_iff, List.all_eq_true, and_assoc] using valid
    refine ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, ?_⟩
    cases hm : results.mapM (fun (table, result) => tableRows schema table result) with
    | error e => simp [hm, bind, Except.bind] at h
    | ok rows =>
      simp only [hm] at h
      change Except.ok (Cedar.Data.Map.make rows.flatten) = Except.ok store at h
      cases h
      exact ⟨rows, mapM_success _ _ _ hm, rfl⟩

/-- SQL の NULL は属性を省く。NULL でない各セルは、解析されタグのついた Cedar の値を持つ。 -/
def ValueCell (input : Column × Option String)
    (output : Option (Column × Cedar.Spec.Value)) : Prop :=
  match input.2 with
  | none => output = none
  | some stored => ∃ value json, Lean.Json.parse stored = .ok json ∧
      PostgresValue.Decoded json value ∧ output = some (input.1, value)

private theorem AttributeCell.values (input : Column × Option String)
    (output : Option (Column × Cedar.Spec.Value)) (h : AttributeCell input output) :
    ValueCell input output := by
  rcases input with ⟨column, stored⟩
  cases stored with
  | none => exact h
  | some stored =>
    obtain ⟨value, decoded, result⟩ := h
    obtain ⟨json, parsed, tagged⟩ := PostgresValue.decode_success stored value decoded
    exact ⟨value, json, parsed, tagged, result⟩

/-- 入力順の行の構成。NULL でない各属性について JSON のタグの関係を持つ。 -/
def ValueRow (table : Table) (columns : List Column)
    (input : List (Option String)) (output : EntityUID × Row) : Prop :=
  ∃ key values cells, input = some key :: values ∧ key.contains '\x00' = false ∧
    columns.length = values.length ∧
    List.Forall₂ ValueCell (columns.zip values) cells ∧
    output = ((⟨table, key⟩ : EntityUID), Cedar.Data.Map.make (cells.filterMap id))

private theorem DecodedRow.values (table : Table) (columns : List Column)
    (input : List (Option String)) (output : EntityUID × Row)
    (h : DecodedRow table columns input output) : ValueRow table columns input output := by
  obtain ⟨key, values, cells, shape, noNul, length, related, result⟩ := h
  exact ⟨key, values, cells, shape, noNul, length,
    forall₂_imp AttributeCell.values related, result⟩

/-- 日本語: 実tableRows成功時、入力順の各行は非NULLかつNUL無しの主キーを持ち、
NULL属性は欠落する。非NULL属性はJSON解析に成功し、タグ別Decoded関係のCedar値となる。
整数値保存はDecoded.int_valueで得られる。返却行は同じ順序のセルから構成される。
JSON解析器内部・Map検索・外部DB実状態との一致は含まない。 -/
theorem tableRows_values (schema : Authz.Schema) (table : Table) (result : Result)
    (rows : List (EntityUID × Row)) (h : tableRows schema table result = .ok rows) :
    ∃ columns,
      (schema.tables.find? (fun entry => entry.1 == table)).map Prod.snd = some columns ∧
      result.columns = "_nyxis_id" :: columns ∧
      List.Forall₂ (ValueRow table columns) result.rows rows := by
  obtain ⟨columns, found, projection, related⟩ := tableRows_cells schema table result rows h
  exact ⟨columns, found, projection,
    forall₂_imp (DecodedRow.values table columns) related⟩

/-- 日本語: 実restore成功時、入力の各テーブル結果について宣言列と投影が一致し、
入力順の全行・全属性がValueRow/ValueCellのタグ別JSON復号関係を満たす。
それらの行をテーブル結果順に連結したMap.makeが返却Storeそのものである。
Map検索・JSON解析器内部・SQL意味論や外部DB実状態との一致は主張しない。 -/
theorem restore_values (schema : Authz.Schema) (results : List (Table × Result))
    (store : Store) (h : restore schema results = .ok store) :
    ∃ rows, List.Forall₂ (fun entry decoded => ∃ columns,
      (schema.tables.find? (fun table => table.1 == entry.1)).map Prod.snd = some columns ∧
      entry.2.columns = "_nyxis_id" :: columns ∧
      List.Forall₂ (ValueRow entry.1 columns) entry.2.rows decoded) results rows ∧
      store = Cedar.Data.Map.make rows.flatten := by
  obtain ⟨_, _, _, _, rows, related, result⟩ := restore_success schema results store h
  exact ⟨rows, forall₂_imp (fun entry decoded success =>
    tableRows_values schema entry.1 entry.2 decoded success) related, result⟩

end Nyxis.Internal.PostgresSnapshot

import Nyxis.Internal.PostgresSql

/-! Pure decoding of the internal SELECT snapshot (Assumption 1; outside the theorems). An SQL NULL means the attribute is absent;
it never becomes a Cedar value. The whole snapshot is validated before a Store is returned. Map.make must not silently
collapse duplicate primary keys. The caller must read all tables inside the same SERIALIZABLE transaction. This module
executes no SQL, performs no authorization, and returns no data to handlers.
-/
namespace Nyxis.Internal.PostgresSnapshot
open Nyxis Db Cedar.Spec

/-- The text-format result of PostgresSql.selectTable. none is SQL NULL. -/
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

/-- Before building the map, checks the SELECT projection and every row, including duplicates. -/
def tableRows (schema : Authz.Schema) (table : Table) (result : Result) :
    Except String (List (EntityUID × Row)) := do
  -- Reuse the SQL layout validation (including unsupported tables and identifier collisions).
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

/-- Requires exactly one result for each table of the schema. A missing table is not an empty table. The order of
results does not matter. Duplicate, extra and unsupported tables are rejected.
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

/-- Each input cell either omits the attribute (SQL NULL) or decodes successfully. -/
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

/-- The primary key is present and contains no NUL. Attributes keep input order up to Map.make. This describes the
construction and says nothing about the lookup semantics of Cedar maps. -/
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

/-- When the real tableRows succeeds, the projection matches the primary key and the declared columns, and each row in
input order has a non-NULL primary key containing no NUL. The number of attribute cells equals the number of declared
columns; NULL means the attribute is absent, non-NULL becomes the value of a successful real decode, and Map.make in
that order constructs the returned row. The value decoder internals, Map lookup and the semantics of the external DB's
actual state are not included. -/
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

/-- If the real tableRows succeeds, SELECT generation and the table lookup succeeded, and the column order matches the
primary key and the declared columns. The row counts before and after decoding are equal, and the decoded primary keys
have no duplicates. Cell value decoding, Map lookup semantics and agreement with the external DB are not included. -/
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

/-- If the real restore succeeds, the table names of the schema and of the results have no duplicates, their counts are
equal, and every schema table is included in the results. The real tableRows succeeds for each result in input order,
and the Map of those decoded rows concatenated in the same order is exactly the returned Store. Nothing is claimed about
the external DB's actual state, SQL semantics, or Map lookup semantics. -/
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

/-- SQL NULL omits the attribute. Each non-NULL cell has a parsed, tagged Cedar value. -/
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

/-- Construction of a row in input order, with the JSON tag relation for each non-NULL attribute. -/
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

/-- When the real tableRows succeeds, each row in input order has a non-NULL primary key without NUL, and NULL
attributes are absent. Non-NULL attributes parse as JSON successfully and become Cedar values in the per-tag Decoded
relation. Preservation of integer values is obtained from Decoded.int_value. The returned rows are built from the cells
in the same order. The JSON parser internals, Map lookup and agreement with the external DB's actual state are not
included. -/
theorem tableRows_values (schema : Authz.Schema) (table : Table) (result : Result)
    (rows : List (EntityUID × Row)) (h : tableRows schema table result = .ok rows) :
    ∃ columns,
      (schema.tables.find? (fun entry => entry.1 == table)).map Prod.snd = some columns ∧
      result.columns = "_nyxis_id" :: columns ∧
      List.Forall₂ (ValueRow table columns) result.rows rows := by
  obtain ⟨columns, found, projection, related⟩ := tableRows_cells schema table result rows h
  exact ⟨columns, found, projection,
    forall₂_imp (DecodedRow.values table columns) related⟩

/-- When the real restore succeeds, the declared columns and the projection match for each input table result, and every
row and attribute in input order satisfies the per-tag JSON decoding relation ValueRow/ValueCell. Map.make over those
rows concatenated in table-result order is exactly the returned Store. Nothing is claimed about Map lookup, the JSON
parser internals, SQL semantics, or agreement with the external DB's actual state. -/
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

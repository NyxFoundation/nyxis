import Nyxis.Internal.Postgres
import Nyxis.Internal.PostgresSnapshot
import Nyxis.Internal.IOTrace

/-! libpq の SELECT 結果の内部の抽出(Assumption 1。Lean の正常終了の条件は以下で証明する)。ハンドラの API や
SQL の実行は無い。呼び出し側は抽出の間、結果を専有し、すべてのテーブルを 1 つのトランザクションで読む。
-/
namespace Nyxis.Internal.PostgresResult
open LeanPq.Extern Nyxis
open Nyxis.Internal.IOTrace (bind_ok MapSuccess mapM_success)

private def invalid : IO α := throw (IO.userError "Invalid PostgreSQL SELECT result")

/-- PGresult の注入できるビュー。すべての添字は使う前に行列数と照らして検査する。 -/
structure Reader where
  status : IO ExecStatus
  rowCount : IO Int
  columnCount : IO Int
  name : Int → IO String
  format : Int → IO Int
  typeOid : Int → IO LeanPq.Oid
  isNull : Int → Int → IO Int
  value : Int → Int → IO String
  byteLength : Int → Int → IO Int

private def native (action : EIO LeanPq.Error α) : IO α :=
  Internal.native "Invalid PostgreSQL SELECT result" action

/-- 固定の上流 lean-pq の FFI。失敗は結果の内容やサーバの診断を出さない。 -/
def reader (result : PGresult) : Reader where
  status := native (PqResultStatus result)
  rowCount := native (PqNtuples result)
  columnCount := native (PqNfields result)
  name := fun c => native (PqFname result c)
  format := fun c => native (PqFformat result c)
  typeOid := fun c => native (PqFtype result c)
  isNull := fun r c => native (PqGetisnull result r c)
  value := fun r c => native (PqGetvalue result r c)
  byteLength := fun r c => native (PqGetlength result r c)

/-- selectTable が生成した text/text-JSONB の投影そのものだけを受け入れる。
空の結果でもメタデータを検証する。値を読む前に NULL を確かめる: libpq は NULL と空の text の両方に
空文字列を返す。バイト長で C 文字列の切り詰めを捕まえる。
失敗時に部分的なスナップショットは漏れない。不正な主キー・セル・重複も検査する。
-/
def extract (schema : Authz.Schema) (table : Db.Table) (r : Reader) :
    IO PostgresSnapshot.Result := do
  let .ok _ := PostgresSql.selectTable schema table | invalid
  let some (_, columns) := schema.tables.find? (fun entry => entry.1 == table) | invalid
  let names := "_nyxis_id" :: columns
  unless (← r.status) == .tuplesOk do invalid
  let rows ← r.rowCount
  let fields ← r.columnCount
  if rows < 0 || fields != Int.ofNat names.length then invalid
  for (name, i) in names.zipIdx do
    let c := Int.ofNat i
    unless (← r.name c) == name && (← r.format c) == 0 &&
        (← r.typeOid c) == (if i == 0 then 25 else 3802) do invalid
  let values ← (List.range rows.toNat).mapM fun i =>
    (List.range names.length).mapM fun j => do
      let row := Int.ofNat i
      let col := Int.ofNat j
      match ← r.isNull row col with
      | 1 => pure none
      | 0 =>
        let text ← r.value row col
        unless (← r.byteLength row col) == Int.ofNat text.utf8ByteSize do invalid
        return some text
      | _ => invalid
  let result : PostgresSnapshot.Result := ⟨names, values⟩
  let .ok _ := PostgresSnapshot.tableRows schema table result | invalid
  return result

/-- 日本語: 実extractの正常終了なら、SELECT生成とテーブル検索が成功し、
status・行数・列数の取得、全投影列のメタデータ検査、全セル取得がこの順に
連続するIO状態で成功している。statusはtuplesOk、行数は非負、列数は主キーと
宣言列の個数であり、返却結果の列はその投影順、行は取得値そのもの。
同じ返却結果のtableRows復元も成功する。ループ内の個々の検査と取得値の対応、
FFIの返り値と外部DB実状態の一致はこの定理では主張しない。 -/
theorem extract_success (schema : Authz.Schema) (table : Db.Table) (r : Reader)
    (result : PostgresSnapshot.Result) (w w' : Void IO.RealWorld)
    (h : extract schema table r w = .ok result w') :
    ∃ command columns rows decoded w1 w2 w3 w4,
      PostgresSql.selectTable schema table = .ok command ∧
      schema.tables.find? (fun entry => entry.1 == table) = some (table, columns) ∧
      r.status w = .ok .tuplesOk w1 ∧
      r.rowCount w1 = .ok rows w2 ∧
      r.columnCount w2 = .ok (Int.ofNat ("_nyxis_id" :: columns).length) w3 ∧
      0 ≤ rows ∧
      (forIn ("_nyxis_id" :: columns).zipIdx () fun (name, i) _ => do
        let c := Int.ofNat i
        unless (← r.name c) == name && (← r.format c) == 0 &&
            (← r.typeOid c) == (if i == 0 then 25 else 3802) do invalid
        pure (ForInStep.yield ())) w3 = .ok () w4 ∧
      ((List.range rows.toNat).mapM fun i =>
        (List.range ("_nyxis_id" :: columns).length).mapM fun j => do
          let row := Int.ofNat i
          let col := Int.ofNat j
          match ← r.isNull row col with
          | 1 => pure none
          | 0 =>
            let text ← r.value row col
            unless (← r.byteLength row col) == Int.ofNat text.utf8ByteSize do invalid
            return some text
          | _ => invalid) w4 = .ok result.rows w' ∧
      result.columns = "_nyxis_id" :: columns ∧
      PostgresSnapshot.tableRows schema table result = .ok decoded := by
  unfold extract at h
  cases hc : PostgresSql.selectTable schema table with
  | error e => simp only [hc] at h; cases h
  | ok command =>
    simp only [hc] at h
    cases hf : schema.tables.find? (fun entry => entry.1 == table) with
    | none => simp only [hf] at h; cases h
    | some entry =>
      rcases entry with ⟨found, columns⟩
      simp only [hf] at h
      have hfound : found = table := by
        have := List.find?_some hf
        simpa using this
      subst found
      replace h := (bind_ok _ _ _ _ _).mp h
      rcases h with ⟨status, w1, hs, h⟩
      split at h
      · rename_i ht
        have hs' : status = .tuplesOk := by
          cases status <;> first | rfl | cases ht
        subst status
        replace h := (bind_ok _ _ _ _ _).mp h
        rcases h with ⟨rows, w2, hr, h⟩
        replace h := (bind_ok _ _ _ _ _).mp h
        rcases h with ⟨fields, w3, hn, h⟩
        split at h
        · cases h
        · rename_i hd
          have hd' : 0 ≤ rows ∧ fields = Int.ofNat ("_nyxis_id" :: columns).length := by
            simpa [Bool.or_eq_false_iff] using hd
          obtain ⟨hrows, rfl⟩ := hd'
          replace h := (bind_ok _ _ _ _ _).mp h
          rcases h with ⟨done, w4, hm, h⟩
          cases done
          replace h := (bind_ok _ _ _ _ _).mp h
          rcases h with ⟨values, w5, hv, h⟩
          cases hd : PostgresSnapshot.tableRows schema table ⟨"_nyxis_id" :: columns, values⟩ with
          | error e => simp only [hd] at h; cases h
          | ok decoded =>
            simp only [hd] at h
            change EST.Out.ok _ w5 = EST.Out.ok result w' at h
            cases h
            exact ⟨command, columns, rows, decoded, w1, w2, w3, w4,
              rfl, rfl, hs, hr, hn, hrows, hm, hv, rfl, hd⟩
      · obtain ⟨_, _, he, _⟩ := (bind_ok _ _ _ _ _).mp h
        cases he

/-- 投影順のメタデータの読み取りの成功。IO 状態は連続する。
OID は主キーでは PostgreSQL の text、宣言された属性では JSONB。 -/
inductive Metadata (r : Reader) :
    List (String × Nat) → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : Metadata r [] w w
  | cons {name i rest w w1 w2 w3 w'} :
      r.name (Int.ofNat i) w = .ok name w1 →
      r.format (Int.ofNat i) w1 = .ok 0 w2 →
      r.typeOid (Int.ofNat i) w2 = .ok (if i == 0 then 25 else 3802) w3 →
      Metadata r rest w3 w' → Metadata r ((name, i) :: rest) w w'

private def metadataStep (r : Reader) (entry : String × Nat) (_ : PUnit) :
    IO (ForInStep PUnit) := do
  let (name, i) := entry
  let c := Int.ofNat i
  unless (← r.name c) == name && (← r.format c) == 0 &&
      (← r.typeOid c) == (if i == 0 then 25 else 3802) do invalid
  pure (.yield ())

private theorem metadataStep_success (r : Reader) (name : String) (i : Nat)
    (w w' : Void IO.RealWorld) (step : ForInStep PUnit)
    (h : metadataStep r (name, i) () w = .ok step w') :
    step = .yield () ∧ ∃ w1 w2,
      r.name (Int.ofNat i) w = .ok name w1 ∧
      r.format (Int.ofNat i) w1 = .ok 0 w2 ∧
      r.typeOid (Int.ofNat i) w2 = .ok (if i == 0 then 25 else 3802) w' := by
  unfold metadataStep at h
  obtain ⟨actualName, w1, hn, h⟩ := (bind_ok _ _ _ _ _).mp h
  obtain ⟨format, w2, hf, h⟩ := (bind_ok _ _ _ _ _).mp h
  obtain ⟨oid, w3, ho, h⟩ := (bind_ok _ _ _ _ _).mp h
  generalize he : (if i == 0 then (25 : LeanPq.Oid) else 3802) = expected at h ⊢
  split at h
  · rename_i hm
    have hm' : actualName = name ∧ format = 0 ∧ oid = expected := by
      simpa [Bool.and_eq_true, and_assoc] using hm
    obtain ⟨hname, hformat, hoid⟩ := hm'
    change EST.Out.ok (ForInStep.yield ()) w3 = EST.Out.ok step w' at h
    cases h
    exact ⟨rfl, w1, w2, hname ▸ hn, hformat ▸ hf, hoid ▸ ho⟩
  · obtain ⟨_, _, he, _⟩ := (bind_ok _ _ _ _ _).mp h
    cases he

/-- 日本語: SELECT抽出と同じメタデータループが正常終了したなら、投影順に
各列の名前・text形式0・主キーtext/属性JSONBのOIDを取得し、期待値との一致を
検査している。各取得と次の列は連続するIO状態を共有し、空投影は状態を変えない。
これはReaderの返り値の証明であり、FFIと外部DBの一致は含まない。 -/
theorem metadata_success (r : Reader) (entries : List (String × Nat))
    (w w' : Void IO.RealWorld)
    (h : (forIn entries () fun (name, i) _ => do
      let c := Int.ofNat i
      unless (← r.name c) == name && (← r.format c) == 0 &&
          (← r.typeOid c) == (if i == 0 then 25 else 3802) do invalid
      pure (ForInStep.yield ())) w = .ok () w') :
    Metadata r entries w w' := by
  change forIn entries () (metadataStep r) w = .ok () w' at h
  induction entries generalizing w with
  | nil =>
    change EST.Out.ok () w = EST.Out.ok () w' at h
    cases h
    exact .nil _
  | cons entry rest ih =>
    rw [List.forIn_cons] at h
    obtain ⟨step, wm, hs, h⟩ := (bind_ok _ _ _ _ _).mp h
    obtain ⟨he, w1, w2, hn, hf, ho⟩ := metadataStep_success r entry.1 entry.2 w wm step hs
    subst step
    exact .cons hn hf ho (ih wm h)

/-- 日本語: 実extractの正常終了から、status・行数・列数の取得に続く全投影列の
メタデータ検査を取り出す。検査列は返却結果の列そのものであり、主キーから
宣言順に各名前・形式・OIDが一致する。セル取得以降はextract_successが扱う。 -/
theorem extract_metadata (schema : Authz.Schema) (table : Db.Table) (r : Reader)
    (result : PostgresSnapshot.Result) (w w' : Void IO.RealWorld)
    (h : extract schema table r w = .ok result w') :
    ∃ columns rows w1 w2 w3 w4,
      result.columns = "_nyxis_id" :: columns ∧
      r.status w = .ok .tuplesOk w1 ∧
      r.rowCount w1 = .ok rows w2 ∧
      r.columnCount w2 = .ok (Int.ofNat result.columns.length) w3 ∧
      Metadata r result.columns.zipIdx w3 w4 := by
  obtain ⟨command, columns, rows, decoded, w1, w2, w3, w4,
    hc, hf, hs, hr, hn, hrows, hm, hv, hcols, hd⟩ :=
    extract_success schema table r result w w' h
  refine ⟨columns, rows, w1, w2, w3, w4, hcols, hs, hr, ?_, ?_⟩
  · simpa only [hcols] using hn
  · rw [hcols]
    exact metadata_success r _ w3 w4 hm

/-- 1 つのセルの読み取りの成功。NULL では値と長さの読み取りを飛ばす。text はバイト長を検査する。 -/
inductive Cell (r : Reader) (i j : Nat) :
    Option String → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | null {w w'} : r.isNull (Int.ofNat i) (Int.ofNat j) w = .ok 1 w' →
      Cell r i j none w w'
  | text {text w w1 w2 w'} :
      r.isNull (Int.ofNat i) (Int.ofNat j) w = .ok 0 w1 →
      r.value (Int.ofNat i) (Int.ofNat j) w1 = .ok text w2 →
      r.byteLength (Int.ofNat i) (Int.ofNat j) w2 = .ok (Int.ofNat text.utf8ByteSize) w' →
      Cell r i j (some text) w w'

/-- 1 行のセルの列順の読み取り。IO 状態は連続する。 -/
inductive Cells (r : Reader) (i : Nat) :
    List Nat → List (Option String) → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : Cells r i [] [] w w
  | cons {j js v vs w wm w'} : Cell r i j v w wm → Cells r i js vs wm w' →
      Cells r i (j :: js) (v :: vs) w w'

/-- 入力順の行。各行は同じ列を順に読む。 -/
inductive Rows (r : Reader) (columns : List Nat) :
    List Nat → List (List (Option String)) → Void IO.RealWorld → Void IO.RealWorld → Prop where
  | nil (w) : Rows r columns [] [] w w
  | cons {i is row rows w wm w'} : Cells r i columns row w wm →
      Rows r columns is rows wm w' → Rows r columns (i :: is) (row :: rows) w w'

private def cellRead (r : Reader) (i j : Nat) : IO (Option String) := do
  let row := Int.ofNat i
  let col := Int.ofNat j
  match ← r.isNull row col with
  | 1 => pure none
  | 0 =>
    let text ← r.value row col
    unless (← r.byteLength row col) == Int.ofNat text.utf8ByteSize do invalid
    return some text
  | _ => invalid

private theorem cellRead_success (r : Reader) (i j : Nat) (v : Option String)
    (w w' : Void IO.RealWorld) (h : cellRead r i j w = .ok v w') :
    Cell r i j v w w' := by
  unfold cellRead at h
  obtain ⟨flag, w1, hn, h⟩ := (bind_ok _ _ _ _ _).mp h
  split at h
  · change EST.Out.ok none w1 = EST.Out.ok v w' at h
    cases h
    exact .null hn
  · obtain ⟨text, w2, hv, h⟩ := (bind_ok _ _ _ _ _).mp h
    obtain ⟨length, w3, hl, h⟩ := (bind_ok _ _ _ _ _).mp h
    split at h
    · rename_i he
      have he' : length = Int.ofNat text.utf8ByteSize := by simpa using he
      change EST.Out.ok (some text) w3 = EST.Out.ok v w' at h
      cases h
      exact .text hn hv (he' ▸ hl)
    · obtain ⟨_, _, he, _⟩ := (bind_ok _ _ _ _ _).mp h
      cases he
  · cases h

private theorem cells_of_map (r : Reader) (i : Nat) (js values)
    (w w' : Void IO.RealWorld)
    (h : MapSuccess (cellRead r i) js values w w') : Cells r i js values w w' := by
  induction h with
  | nil => exact .nil _
  | cons hs ht ih => exact .cons (cellRead_success _ _ _ _ _ _ hs) ih

private theorem rows_of_map (r : Reader) (columns : List Nat) (indices values)
    (w w' : Void IO.RealWorld)
    (h : MapSuccess (fun i => columns.mapM (cellRead r i)) indices values w w') :
    Rows r columns indices values w w' := by
  induction h with
  | nil => exact .nil _
  | cons hs ht ih => exact .cons (cells_of_map _ _ _ _ _ _ (mapM_success _ _ _ _ _ hs)) ih

/-- 日本語: 二重mapMで全セルを正常に取得できたなら、入力の行順・列順に
NULL判定が成功し、非NULLセルではvalue取得とUTF-8バイト長の一致検査も成功する。
各取得は連続するIO状態を共有し、返却セルはNULLならnone、それ以外は取得文字列。
Readerの返り値についての主張であり、外部DBの実状態との一致は含まない。 -/
theorem cells_success (r : Reader) (indices columns : List Nat) (values)
    (w w' : Void IO.RealWorld)
    (h : (indices.mapM fun i => columns.mapM fun j => do
      let row := Int.ofNat i
      let col := Int.ofNat j
      match ← r.isNull row col with
      | 1 => pure none
      | 0 =>
        let text ← r.value row col
        unless (← r.byteLength row col) == Int.ofNat text.utf8ByteSize do invalid
        return some text
      | _ => invalid) w = .ok values w') :
    Rows r columns indices values w w' :=
  rows_of_map r columns indices values w w' (mapM_success _ _ _ _ _ h)

private theorem cells_length (r : Reader) (i js values w w')
    (h : Cells r i js values w w') : values.length = js.length := by
  induction h with
  | nil => rfl
  | cons hs ht ih => simp only [List.length_cons, ih]

/-- 日本語: セル取得成功列は行数を保存し、すべての返却行の列数は入力列数に等しい。
空の行列も含む。NULLセルも1列として数える。 -/
theorem rows_dimensions (r : Reader) (columns indices values w w')
    (h : Rows r columns indices values w w') :
    values.length = indices.length ∧ ∀ row ∈ values, row.length = columns.length := by
  induction h with
  | nil => simp
  | cons hs ht ih =>
    exact ⟨congrArg Nat.succ ih.1, by
      intro row hm
      rcases List.mem_cons.mp hm with he | hm
      · subst row; exact cells_length _ _ _ _ _ _ hs
      · exact ih.2 row hm⟩

/-- 日本語: 実extractの正常終了から全セルのNULL/値/バイト長と返却値の対応を
行順・列順の連続IO状態で取り出す。返却行数はReaderの非負行数と一致し、
各返却行の列数は返却投影列数と一致する。セル復号と外部DB実状態は主張しない。 -/
theorem extract_cells (schema : Authz.Schema) (table : Db.Table) (r : Reader)
    (result : PostgresSnapshot.Result) (w w' : Void IO.RealWorld)
    (h : extract schema table r w = .ok result w') :
    ∃ rows w1 w2 w3 wm,
      r.status w = .ok .tuplesOk w1 ∧
      r.rowCount w1 = .ok rows w2 ∧
      r.columnCount w2 = .ok (Int.ofNat result.columns.length) w3 ∧
      0 ≤ rows ∧ Metadata r result.columns.zipIdx w3 wm ∧
      Rows r (List.range result.columns.length) (List.range rows.toNat) result.rows wm w' ∧
      result.rows.length = rows.toNat ∧
      (∀ row ∈ result.rows, row.length = result.columns.length) := by
  obtain ⟨command, columns, rows, decoded, w1, w2, w3, w4,
    hc, hf, hs, hr, hn, hrows, hm, hv, hcols, hd⟩ :=
    extract_success schema table r result w w' h
  have ht := cells_success r (List.range rows.toNat)
    (List.range ("_nyxis_id" :: columns).length) result.rows w4 w' hv
  rw [← hcols] at ht
  obtain ⟨hlen, hwidth⟩ := rows_dimensions _ _ _ _ _ _ ht
  exact ⟨rows, w1, w2, w3, w4, hs, hr, by simpa only [hcols] using hn, hrows,
    by rw [hcols]; exact metadata_success r _ w3 w4 hm,
    ht, by simpa using hlen, by simpa using hwidth⟩

end Nyxis.Internal.PostgresResult

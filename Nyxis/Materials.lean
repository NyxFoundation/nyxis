import Nyxis.Db
import Cedar.Validation
import Cedar.Thm.Validation.Levels
import Cedar.Thm.Validation.RequestEntityValidation
import Cedar.Thm.Validation.Slice

/-!
# Nyxis.Materials — 判定材料

認可層(`Nyxis.Authz`)は、DB の現在の行を Cedar の実体にして判定する。一覧以外の要求では判定に必要な
実体(主体の行・対象の行・ポリシーが参照する実体)だけを DB から取得する。取得した実体だけで行った判定は
全テーブルを取得した場合の判定と一致しなければならない。このモジュールは、その一致を cedar-lean の既存定理に結ぶ
(評価器も検証器も自前で再実装しない)。

- cedar-lean の **level 検証**(`Cedar.Validation.validateWithLevel policies ts n`)は、各ポリシーが実体の属性を
  最大 `n` 段しか辿らないことを型検査で確かめる。`levelOf` は正本のポリシーが通る最小の level を探す。
- cedar-lean の **slicing 定理**(`Cedar.Thm.validate_with_level_is_sound_wf`)は、level `n` で検証に通った
  ポリシー集合について、`isAuthorized` の結果が全実体と `Entities.sliceAtLevel req n`(要求の主体・アクション・
  対象・文脈に現れる実体から `n` 段で到達できる実体だけ)で一致することを述べる。
- その前提は、型環境が well-formed(`Schema.validateWellFormed`)、要求がある環境のインスタンス
  (`validateRequest`)、**全実体がスキーマのインスタンス**(`Cedar.Thm.InstanceOfSchema`)の 3 つ。前 2 つは
  `Authz.step` が判定ごとに実行可能な検査として確かめる(通らなければ拒否する)。3 つめは、判定の実体
  (`entities`)を「DB の行のうちスキーマに適合する行(`conforms`)+ スキーマの全アクションの実体」として
  組み立てることで、どんな DB の状態についても構成から成り立つ(`instanceOfSchema_entities`)。主定理に新しい
  仮定は置かない。
- **部分的な取得**(`Known`): 実 DB から主キーの点検索で取得した行と、引いたが無かった実体の記録。取得が全体の
  状態と整合し(`Known.Consistent`)、要求から到達できる実体をすべて取得済みなら(`closedAt`: 実行可能な検査)、
  取得した行だけから組んだ判定材料の slice は全体から組んだ slice と等しい(`sliceAtLevel_eq`)。
  `Nyxis.Authz.permits_eq_of_covers` / `step_eq_of_covers` がこれを認可層の判定と `step` の結果の一致に結ぶ。
  接続層(PostgreSQL の点検索。`PostgresRun.runStaged`)はこの `Known` を組み立て、この検査を通してから判定する。

適合しない行(列の型や必須の列がスキーマと合わない行)は判定の実体に現れない。そのような行は、nyxis が正本から
DDL を作り、書き込みを形状検査で拒み、DB へは nyxis 専用ロール以外から到達できない(`ASSUMPTIONS.md` Assumption 2・3)ことから
実際には生じず、実 DB の接続層(`PostgresRun`)は取得した行の形状検査に失敗すれば要求全体を 503 で閉じる。
アクションの実体は属性・tag を持たず祖先は宣言どおりで、cedar-lean の実体の整合(`Entities.HasAllActions`)が
全アクションの存在を要求するために加える。アクション群(`action "a" in [Action::"g"]`)の `in` はこの祖先で判定される。

行の実体の祖先(実体の親): 正本が `entity T in [P]` と宣言し `@parents("列, …")` で親を指す列を添えたテーブルでは、
行の実体はその列の値(実体、または実体の集合の要素)のうち宣言された親の型のものを祖先として持つ
(`rowAncestors`)。ポリシーの `principal in resource.org`(主体が対象の組織のメンバーなら)はこの祖先で判定される。
祖先の型が宣言どおりであることは構成から成り立つ(`rowAncestors_ty`)。cedar-lean の slicing は祖先を辿らない
(`EntityData.sliceEUIDs` は属性と tag だけ)ので、`in` の判定に親の行は要らない。Cedar の `in`(評価 `inₑ`・型付け
`descendentOf`)は祖先の集合が推移的に閉じていることを前提にするので、正本の検査は親の型がさらに親を持つ(多段)ことと
自己参照を拒む(`Nyxis.CedarSchema.entityEntry`): 直接の親だけなら推移閉包と一致する。

所属行(多対多の所属を別テーブルの行で表す): 正本が `entity T in [P]` に `@memberships("M: 列 -> 列, …")` を
添えると、テーブル `M`(所属行のテーブル)の行のうち列 `M.列`(所属する側)の値が `T::"k"` である行の、親を指す列の値
(`P` か `Set<P>`)も、行 `T::"k"` の実体の祖先になる(`membershipRefs`)。この祖先は他の行(所属行)に依るので、判定の
実体の一致(`entities_find?_eq`)には、その実体の所属行の全部(所属行のテーブルの行のうち所属する側の列がその実体である
行。`matchingRows`: 絞り込みに合う行)が両方の状態で同じ(行の集合として同じ: 順序は `Set.make` が吸収する)ことが要る。
部分的な取得 `Known` は「絞り込みに合う行をすべて取得した」記録 `fetched` を持ち(接続層では WHERE 句つきの SELECT)、
`Known.knows` は型に所属行の宣言があるテーブルの実体について、行の有無に加えてその所属行の取得(`coversMemberships`)を
要求する。
-/

deriving instance DecidableEq for Cedar.Validation.ActionSchemaEntry
deriving instance DecidableEq for Cedar.Validation.Schema

namespace Nyxis.Materials

open Cedar.Spec
open Cedar.Data
open Nyxis.Db

/-! ## `Map` と `Store` の補題 -/

/-- `find?` は、鍵が一致する最初の組の値。 -/
theorem map_find?_eq_list_find? {α β : Type} [BEq α] (m : Map α β) (k : α) :
    m.find? k = (m.toList.find? (fun x => x.fst == k)).map Prod.snd := by
  simp only [Map.find?]
  split
  · rename_i v h
    rw [h]
    rfl
  · rename_i h
    cases hf : m.toList.find? (fun x => x.fst == k) with
    | none => rfl
    | some p => exact absurd hf (h p.1 p.2)

private theorem find?_filter_ne {l : List (EntityUID × Row)} {u tk : EntityUID} (hne : u ≠ tk) :
    (l.filter (fun kv => kv.1 != tk)).find? (fun kv => kv.1 == u) = l.find? (fun kv => kv.1 == u) := by
  induction l with
  | nil => rfl
  | cons kv rest ih =>
    rw [List.filter_cons]
    by_cases h : kv.1 = u
    · subst h
      have hk : (kv.1 != tk) = true := by simpa using hne
      rw [ite_eq_left hk, List.find?_cons_of_pos (p := fun x : EntityUID × Row => x.1 == kv.1) (a := kv) (by simp),
        List.find?_cons_of_pos (p := fun x : EntityUID × Row => x.1 == kv.1) (a := kv) (by simp)]
    · have hk : ¬ ((fun x : EntityUID × Row => x.1 == u) kv = true) := by simpa using h
      rw [List.find?_cons_of_neg (p := fun x : EntityUID × Row => x.1 == u) (a := kv) hk]
      by_cases ht : kv.1 = tk
      · have ht' : ¬ ((kv.1 != tk) = true) := by simpa using ht
        rw [ite_eq_right ht', ih]
      · have ht' : (kv.1 != tk) = true := by simpa using ht
        rw [ite_eq_left ht', List.find?_cons_of_neg (p := fun x : EntityUID × Row => x.1 == u) (a := kv) hk, ih]

/-- 行を置いた後の `find?`: 置いた主キーならその行、それ以外は元のまま。 -/
theorem find?_put (s : Store) (t : Table) (k : Key) (row : Row) (u : EntityUID) :
    Map.find? (s.put t k row) u = if u = ⟨t, k⟩ then some row else Map.find? s u := by
  unfold Store.put
  rw [Map.make_find?_eq_list_find?, map_find?_eq_list_find?]
  split
  · rename_i heq
    subst heq
    simp
  · rename_i hne
    have h : ((⟨t, k⟩ : EntityUID) == u) = false := by simpa using Ne.symm hne
    rw [List.find?_cons_of_neg (by simp [h]), find?_filter_ne hne]

/-! ## `Map.make` は鍵を落とさない -/

theorem insertCanonical_key {α β : Type} [LT α] [StrictLT α] [DecidableLT α] (x : α × β) :
    ∀ (ys : List (α × β)) (k : α) (v : β), (k, v) ∈ ys →
      ∃ v', (k, v') ∈ List.insertCanonical Prod.fst x ys
  | [], _, _, h => by simp at h
  | y :: ys, k, v, h => by
    simp only [List.insertCanonical]
    split
    · exact ⟨v, List.mem_cons_of_mem _ h⟩
    · split
      · rcases List.mem_cons.mp h with hy | hys
        · exact ⟨v, by rw [hy]; exact List.mem_cons_self⟩
        · obtain ⟨v', hv'⟩ := insertCanonical_key x ys k v hys
          exact ⟨v', List.mem_cons_of_mem _ hv'⟩
      · rename_i hlt hgt
        rcases List.mem_cons.mp h with hy | hys
        · have hk : x.1 = y.1 := by
            by_contra hne
            rcases StrictLT.connected x.1 y.1 hne with hlt' | hgt'
            · exact hlt hlt'
            · exact hgt hgt'
          have hky : k = y.1 := by rw [← hy]
          refine ⟨x.2, ?_⟩
          rw [hky, ← hk]
          exact List.mem_cons_self
        · exact ⟨v, List.mem_cons_of_mem _ hys⟩

theorem canonicalize_key {α β : Type} [LT α] [StrictLT α] [DecidableLT α] :
    ∀ (xs : List (α × β)) (k : α) (v : β), (k, v) ∈ xs →
      ∃ v', (k, v') ∈ List.canonicalize Prod.fst xs
  | [], _, _, h => by simp at h
  | x :: xs, k, v, h => by
    simp only [List.canonicalize]
    rcases List.mem_cons.mp h with hx | hxs
    · exact ⟨v, by rw [hx]; exact List.insertCanonical_mem x⟩
    · obtain ⟨v', hv'⟩ := canonicalize_key xs k v hxs
      exact insertCanonical_key x _ k v' hv'

/-- リストにある鍵は `Map.make` の後も引ける(値はそのうちの 1 つ)。 -/
theorem find?_make_of_mem {α β : Type} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α]
    {xs : List (α × β)} {k : α} {v : β} (h : (k, v) ∈ xs) :
    ∃ v', (Map.make xs).find? k = some v' := by
  obtain ⟨v', hv'⟩ := canonicalize_key xs k v h
  refine ⟨v', (Map.in_list_iff_find?_some (Map.make_wf xs)).mp ?_⟩
  rw [Map.toList_make_eq_canonicalize]
  exact hv'

/-- 鍵ごとに値が一意なリストでは、`Map.make` の `find?` はリストの組そのもの。 -/
theorem find?_make_iff_mem {α β : Type} [LT α] [StrictLT α] [DecidableLT α] [DecidableEq α]
    {xs : List (α × β)} (hfun : ∀ k v v', (k, v) ∈ xs → (k, v') ∈ xs → v = v') (k : α) (v : β) :
    (Map.make xs).find? k = some v ↔ (k, v) ∈ xs := by
  constructor
  · intro h
    exact Map.mem_make_mem_list (Map.find?_mem_toList h)
  · intro h
    obtain ⟨v', hv'⟩ := find?_make_of_mem h
    have hmem := Map.mem_make_mem_list (Map.find?_mem_toList hv')
    rw [hfun k v v' h hmem]
    exact hv'

/-! ## 判定の実体 -/

/-- 行がスキーマに適合するか: 主キーがアクションの UID ではなく、テーブル(エンティティ型)が型環境にあり、
    主キーがその型の ID として有効で、列の値が宣言された属性の型のインスタンスである(cedar-lean の
    `instanceOfType`)。アクションの実体は `actionEntries` が別に与えるので、行とアクションが同じ UID を持つ
    ことはない(well-formed な型環境ではアクションの型はエンティティ型にならないので、この除外は判定を変えない)。 -/
def conforms (ts : Cedar.Validation.Schema) (uid : EntityUID) (row : Row) : Bool :=
  (ts.acts.find? uid).isNone &&
  match ts.ets.find? uid.ty with
  | some entry =>
    entry.isValidEntityEID uid.eid &&
      Cedar.Validation.instanceOfType (.record row) (.record entry.attrs) ts
  | none => false

/-- 親を指す列: テーブルごとの、その行の親(Cedar の実体の祖先。ポリシーの `in` で判定する)を指す列の名前。
    正本の `entity T in [P]` に添えた `@parents("列, …")` から構成する(`Nyxis.CedarSchema`)。 -/
abbrev ParentColumns := List (EntityType × List Attr)

/-- 値に現れる実体の参照: 実体そのもの(`P` 型の列)か、集合の要素(`Set<P>` 型の列)。親を指す列の型は正本の検査で
    この 2 つに限る(`Nyxis.CedarSchema`)。 -/
def entityRefs : Value → List EntityUID
  | .prim (.entityUID uid) => [uid]
  | .set s => s.toList.filterMap fun
    | .prim (.entityUID uid) => some uid
    | _ => none
  | _ => []

/-- 所属行の宣言: テーブル `table` の行のうち列 `member` の値がある実体を指す行が、その実体の所属行。
    所属行の列 `parents`(親の型 `P` か `Set<P>`)の値が、その実体の祖先になる。正本の `entity T in [P]` に添えた
    `@memberships("M: 列 -> 列, …")` から構成する(`Nyxis.CedarSchema`)。 -/
structure Membership where
  /-- 所属行のテーブル。 -/
  table : Table
  /-- 所属する側(祖先を得る実体)を指す列。型はその実体の型。 -/
  member : Attr
  /-- 親を指す列。型は親の型 `P` か `Set<P>`。 -/
  parents : List Attr
  deriving Repr, DecidableEq

/-- 所属行の宣言: 所属する側のテーブル(エンティティ型)ごと。 -/
abbrev MembershipColumns := List (EntityType × List Membership)

/-- テーブル `table` の現在の行のうち絞り込みに合う行。一覧の候補、一意性・参照整合の判定、所属行が
    この経路で行を見る(実 DB では WHERE 句つきの SELECT)。 -/
def matchingRows (store : Store) (table : Table) (filters : List Filter) : List (Key × Row) :=
  (store.rows table).filter fun kv => Filter.matchesAll filters kv.2

/-- 実体 `uid` の所属行の絞り込み: 所属する側の列が `uid` である行。 -/
def Membership.filterOf (m : Membership) (uid : EntityUID) : List Filter :=
  [⟨m.member, .eq, .prim (.entityUID uid)⟩]

/-- 実体 `uid` の所属行から得る親の参照: 型の各宣言について、その所属行の親を指す列の値に現れる実体。 -/
def membershipRefs (mc : MembershipColumns) (store : Store) (uid : EntityUID) : List EntityUID :=
  ((mc.lookup uid.ty).getD []).flatMap fun m =>
    (matchingRows store m.table (m.filterOf uid)).flatMap fun kv =>
      m.parents.flatMap fun c => ((Map.find? kv.2 c).map entityRefs).getD []

/-- 行の親(実体の祖先): 親を指す列の値に現れる実体と、所属行の親を指す列の値に現れる実体のうち、型環境がその型の
    祖先の型として宣言しているもの。行の実体はこの集合を祖先として持ち、ポリシーの `principal in resource.org` の
    ような判定はこれを見る。親を指す列も所属行も無いテーブル(1 つめの公式サンプル)では空。祖先の祖先は辿らない
    (`in` は正本に宣言した直接の親についてだけ成り立つ)。 -/
def rowAncestors (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store)
    (uid : EntityUID) (row : Row) : Set EntityUID :=
  match ts.ets.find? uid.ty with
  | some entry =>
    let cols := (pc.lookup uid.ty).getD []
    Set.make (((cols.flatMap fun c => ((Map.find? row c).map entityRefs).getD []) ++ membershipRefs mc store uid).filter
      fun p => entry.ancestors.contains p.ty)
  | none => Set.empty

/-- 行の実体。列が属性になり、親を指す列と所属行の値が祖先になり、tag は持たない。 -/
def rowData (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store)
    (uid : EntityUID) (row : Row) : EntityData :=
  { attrs := row, ancestors := rowAncestors ts pc mc store uid row, tags := Map.empty }

/-- DB の状態のうち、スキーマに適合する行の実体(主キー順は `Store` のまま)。行はその主キーで `find?` を引き直す
    (`Store.rows` と同じ経路。同じ主キーが重複していても `find?` の行だけが実体になる)。 -/
def rowEntries (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store) :
    List (EntityUID × EntityData) :=
  store.toList.filterMap fun kv =>
    match Map.find? store kv.1 with
    | some row => if conforms ts kv.1 row then some (kv.1, rowData ts pc mc store kv.1 row) else none
    | none => none

/-- スキーマの全アクションの実体。属性・tag は無く、祖先は宣言どおり(`actionSchemaEntryToEntityData`)。
    各アクションの項目は型環境の `find?` で引く(重複した宣言があっても `find?` と同じ項目になる)。 -/
def actionEntries (ts : Cedar.Validation.Schema) : List (EntityUID × EntityData) :=
  ts.acts.toList.filterMap fun kv =>
    (ts.acts.find? kv.1).map fun entry => (kv.1, Cedar.Validation.actionSchemaEntryToEntityData entry)

/-- 判定の実体: DB の状態のうちスキーマに適合する行(親を指す列と所属行の値を祖先に持つ)と、スキーマの全アクション。 -/
def entities (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store) : Entities :=
  Map.make (rowEntries ts pc mc store ++ actionEntries ts)

theorem mem_rowEntries (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store)
    (u : EntityUID) (d : EntityData) :
    (u, d) ∈ rowEntries ts pc mc store ↔
      ∃ row, Map.find? store u = some row ∧ conforms ts u row = true ∧ d = rowData ts pc mc store u row := by
  simp only [rowEntries, List.mem_filterMap]
  constructor
  · rintro ⟨⟨u', r⟩, _, hsome⟩
    split at hsome
    · rename_i row hfind
      split at hsome
      · rename_i hconf
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        exact ⟨row, hfind, hconf, rfl⟩
      · cases hsome
    · cases hsome
  · rintro ⟨row, hfind, hconf, rfl⟩
    exact ⟨(u, row), Map.find?_mem_toList hfind, by simp [hfind, hconf]⟩

theorem mem_actionEntries (ts : Cedar.Validation.Schema) (u : EntityUID) (d : EntityData) :
    (u, d) ∈ actionEntries ts ↔
      ∃ entry, ts.acts.find? u = some entry ∧ d = Cedar.Validation.actionSchemaEntryToEntityData entry := by
  simp only [actionEntries, List.mem_filterMap]
  constructor
  · rintro ⟨⟨u', e'⟩, _, hsome⟩
    simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hsome
    obtain ⟨entry, hfind, rfl, rfl⟩ := hsome
    exact ⟨entry, hfind, rfl⟩
  · rintro ⟨entry, hfind, rfl⟩
    exact ⟨(u, entry), Map.find?_mem_toList hfind, by simp [hfind]⟩

/-- 判定の実体の組は鍵ごとに一意(行は `find?` の行、アクションは `find?` の項目、両者の UID は重ならない)。 -/
theorem entries_functional (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (store : Store) :
    ∀ k v v', (k, v) ∈ rowEntries ts pc mc store ++ actionEntries ts →
      (k, v') ∈ rowEntries ts pc mc store ++ actionEntries ts → v = v' := by
  intro k v v' h h'
  simp only [List.mem_append, mem_rowEntries, mem_actionEntries] at h h'
  rcases h with ⟨row, hr, hc, rfl⟩ | ⟨entry, he, rfl⟩ <;>
    rcases h' with ⟨row', hr', hc', rfl⟩ | ⟨entry', he', rfl⟩
  · rw [hr] at hr'
    cases hr'
    rfl
  · unfold conforms at hc
    simp only [Bool.and_eq_true] at hc
    rw [he'] at hc
    cases hc.1
  · unfold conforms at hc'
    simp only [Bool.and_eq_true] at hc'
    rw [he] at hc'
    cases hc'.1
  · rw [he] at he'
    cases he'
    rfl

/-- 判定の実体の `find?`: 適合する現在の行か、スキーマのアクション。 -/
theorem entities_find?_iff (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (store : Store) (u : EntityUID) (d : EntityData) :
    (entities ts pc mc store).find? u = some d ↔
      (∃ row, Map.find? store u = some row ∧ conforms ts u row = true ∧ d = rowData ts pc mc store u row) ∨
      (∃ entry, ts.acts.find? u = some entry ∧ d = Cedar.Validation.actionSchemaEntryToEntityData entry) := by
  unfold entities
  rw [find?_make_iff_mem (entries_functional ts pc mc store)]
  simp only [List.mem_append, mem_rowEntries, mem_actionEntries]

/-- `(key, row)` がテーブルの現在の行列にあるのは、その主キーで `find?` を引いた現在の行がそれであるとき、
    そのときに限る(`Store.rows` は主キーを `toList` から取り、行は `find?` で引き直す)。 -/
theorem mem_rows_iff (s : Store) (table : Table) (key : Key) (row : Row) :
    (key, row) ∈ s.rows table ↔ Map.find? s ⟨table, key⟩ = some row := by
  constructor
  · exact Store.rows_find? s table key row
  · intro hfind
    simp only [Store.rows, List.mem_filterMap]
    refine ⟨key, ?_, by simp [Store.find?, hfind]⟩
    exact ⟨(⟨table, key⟩, row), Map.find?_mem_toList hfind, by simp⟩

/-- 絞り込みに合う行列の要素: その主キーの現在の行で、絞り込みに合うもの。 -/
theorem mem_matchingRows_iff (s : Store) (table : Table) (filters : List Filter) (kv : Key × Row) :
    kv ∈ matchingRows s table filters ↔
      Map.find? s ⟨table, kv.1⟩ = some kv.2 ∧ Filter.matchesAll filters kv.2 = true := by
  obtain ⟨key, row⟩ := kv
  simp only [matchingRows, List.mem_filter, mem_rows_iff]

/-- 2 つの状態で、絞り込みに合う行列が集合として同じであること。 -/
def RowsAgree (s₁ s₂ : Store) (table : Table) (filters : List Filter) : Prop :=
  ∀ kv, kv ∈ matchingRows s₁ table filters ↔ kv ∈ matchingRows s₂ table filters

/-- 実体の所属行が 2 つの状態で集合として同じなら、所属行から得る親の参照も集合として同じ。 -/
theorem membershipRefs_mem (mc : MembershipColumns) (s₁ s₂ : Store) (u : EntityUID)
    (hm : ∀ m ∈ (mc.lookup u.ty).getD [], RowsAgree s₁ s₂ m.table (m.filterOf u)) (x : EntityUID) :
    x ∈ membershipRefs mc s₁ u ↔ x ∈ membershipRefs mc s₂ u := by
  simp only [membershipRefs, List.mem_flatMap]
  constructor
  · rintro ⟨m, hmem, kv, hkv, hx⟩
    exact ⟨m, hmem, kv, (hm m hmem kv).mp hkv, hx⟩
  · rintro ⟨m, hmem, kv, hkv, hx⟩
    exact ⟨m, hmem, kv, (hm m hmem kv).mpr hkv, hx⟩

/-- 実体の所属行が 2 つの状態で集合として同じなら、行の実体は同じ(祖先は `Set.make` なので順序に依らない)。 -/
theorem rowData_eq (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (s₁ s₂ : Store)
    (u : EntityUID) (row : Row)
    (hm : ∀ m ∈ (mc.lookup u.ty).getD [], RowsAgree s₁ s₂ m.table (m.filterOf u)) :
    rowData ts pc mc s₁ u row = rowData ts pc mc s₂ u row := by
  simp only [rowData, rowAncestors]
  split
  · congr 1
    apply Set.make_make_eqv.mpr
    simp only [List.Equiv, List.subset_def, List.mem_filter, List.mem_append]
    constructor <;> intro x hx <;> refine ⟨?_, hx.2⟩
    · rcases hx.1 with h | h
      · exact Or.inl h
      · exact Or.inr ((membershipRefs_mem mc s₁ s₂ u hm x).mp h)
    · rcases hx.1 with h | h
      · exact Or.inl h
      · exact Or.inr ((membershipRefs_mem mc s₁ s₂ u hm x).mpr h)
  · rfl

/-- 型環境のテーブルの UID について 2 つの状態の `find?` が一致し、その実体の所属行が集合として同じなら、
    判定の実体の `find?` も一致する(テーブルでない型の UID は行の実体にならないので、状態に依らない)。 -/
theorem entities_find?_eq (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (s₁ s₂ : Store) (u : EntityUID)
    (h : (ts.ets.find? u.ty).isSome = true → Map.find? s₁ u = Map.find? s₂ u)
    (hm : (ts.ets.find? u.ty).isSome = true →
      ∀ m ∈ (mc.lookup u.ty).getD [], RowsAgree s₁ s₂ m.table (m.filterOf u)) :
    (entities ts pc mc s₁).find? u = (entities ts pc mc s₂).find? u := by
  apply Option.ext
  intro d
  rw [entities_find?_iff, entities_find?_iff]
  cases hty : ts.ets.find? u.ty with
  | none =>
    have hconf : ∀ row, conforms ts u row = false := by
      intro row
      unfold conforms
      rw [hty]
      simp
    simp [hconf]
  | some entry =>
    have htab : (ts.ets.find? u.ty).isSome = true := by rw [hty]; rfl
    rw [h htab]
    simp only [rowData_eq ts pc mc s₁ s₂ u _ (hm htab)]

/-! ## 判定ごとの前提の検査 -/

/-- 探す level の上限。判定材料は要求に現れる実体から高々この段数で到達できる実体に限られる。 -/
def maxLevel : Nat := 4

/-- 正本のポリシーが cedar-lean の level 検証に通る最小の level(0 〜 `maxLevel`)。無ければ `none`
    (`Authz.step` はそのとき拒否する)。 -/
def levelOf (policies : Policies) (ts : Cedar.Validation.Schema) : Option Nat :=
  (List.range (maxLevel + 1)).find? fun level =>
    match Cedar.Validation.validateWithLevel policies ts level with
    | .ok _ => true
    | .error _ => false

/-- 判定ごとに実行可能な前提: 型環境が well-formed で、要求(主体・アクション・対象・文脈)がスキーマのある環境の
    インスタンスである。実体の適合性は `entities` の構成で保証されるので検査しない。 -/
def premisesHold (ts : Cedar.Validation.Schema) (req : Request) : Bool :=
  (match ts.validateWellFormed with | .ok _ => true | .error _ => false) &&
  (match Cedar.Validation.validateRequest ts req with | .ok _ => true | .error _ => false)

theorem levelOf_spec {policies : Policies} {ts : Cedar.Validation.Schema} {level : Nat}
    (h : levelOf policies ts = some level) :
    Cedar.Validation.validateWithLevel policies ts level = .ok () := by
  have hp := List.find?_some h
  revert hp
  split
  · rename_i u heq; cases u; exact fun _ => heq
  · intro h; cases h

theorem premisesHold_spec {ts : Cedar.Validation.Schema} {req : Request} (h : premisesHold ts req = true) :
    ts.validateWellFormed = .ok () ∧ Cedar.Validation.validateRequest ts req = .ok () := by
  simp only [premisesHold, Bool.and_eq_true] at h
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨?_, ?_⟩
  · revert h₁; split
    · rename_i u heq; cases u; exact fun _ => heq
    · intro h; cases h
  · revert h₂; split
    · rename_i u heq; cases u; exact fun _ => heq
    · intro h; cases h

/-! ## 構成による実体の適合性 -/

/-- 行の祖先の型は、型環境がその型の祖先として宣言した型である(構成による: `rowAncestors` はそれ以外を落とす。
    所属行から得た参照も同じ)。 -/
theorem rowAncestors_ty (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns) (store : Store)
    (uid : EntityUID) (row : Row)
    (entry : Cedar.Validation.EntitySchemaEntry) (hentry : ts.ets.find? uid.ty = some entry)
    (anc : EntityUID) (hanc : anc ∈ rowAncestors ts pc mc store uid row) : anc.ty ∈ entry.ancestors := by
  unfold rowAncestors at hanc
  rw [hentry] at hanc
  simp only [Set.mem_make, List.mem_filter] at hanc
  exact Set.contains_prop_bool_equiv.mp hanc.2

/-- 判定の実体 `entities ts pc mc store` は、どんな DB の状態についても、型環境 `ts` の各環境のインスタンスである
    (cedar-lean の `InstanceOfSchema`): 各実体は適合する行(祖先の型は宣言どおり)かスキーマのアクションで、
    全アクションが存在する。 -/
theorem instanceOfSchema_entities (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (env : Cedar.Validation.TypeEnv) (store : Store) (hets : env.ets = ts.ets) (hacts : env.acts = ts.acts) :
    Cedar.Thm.InstanceOfSchema (entities ts pc mc store) env := by
  constructor
  · intro uid data hfind
    rcases (entities_find?_iff ts pc mc store uid data).mp hfind with ⟨row, _, hconf, rfl⟩ | ⟨entry, hfind', rfl⟩
    · left
      unfold conforms at hconf
      simp only [Bool.and_eq_true] at hconf
      obtain ⟨_, hconf⟩ := hconf
      split at hconf
      · rename_i entry hentry
        simp only [Bool.and_eq_true] at hconf
        obtain ⟨hvalid, htype⟩ := hconf
        refine ⟨entry, by rw [hets]; exact hentry, ?_, ?_, ?_, ?_⟩
        · cases entry with
          | standard _ => simp [Cedar.Thm.IsValidEntityEID]
          | enum eids =>
            simp only [Cedar.Validation.EntitySchemaEntry.isValidEntityEID] at hvalid
            simp only [Cedar.Thm.IsValidEntityEID]
            exact Set.contains_prop_bool_equiv.mp hvalid
        · apply Cedar.Thm.instance_of_type_refl
          have hschema : env.schema = ts := by
            show Cedar.Validation.Schema.mk env.ets env.acts = ts
            rw [hets, hacts]
          rw [hschema]
          exact htype
        · intro anc hanc
          exact rowAncestors_ty ts pc mc store uid row entry hentry anc hanc
        · unfold Cedar.Thm.InstanceOfEntityTags
          split
          · intro v hv
            simp [rowData, Map.values, Map.empty, Map.toList] at hv
          · rfl
      · cases hconf
    · right
      exact ⟨rfl, rfl, entry, by rw [hacts]; exact hfind', rfl⟩
  · intro uid entry hfind
    rw [hacts] at hfind
    have hmem : (uid, Cedar.Validation.actionSchemaEntryToEntityData entry) ∈ actionEntries ts := by
      simp only [actionEntries, List.mem_filterMap]
      exact ⟨(uid, entry), Map.find?_mem_toList hfind, by simp [hfind]⟩
    exact find?_make_of_mem (List.mem_append_right _ hmem)

/-- 型環境が well-formed で要求がある環境のインスタンスなら、判定の実体はその環境のもとで cedar-lean の
    slicing 定理の前提(`InstanceOfWellFormedSchema`)を満たす。 -/
theorem instanceOfWellFormedSchema (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (store : Store) (req : Request)
    (hwf : ts.validateWellFormed = .ok ())
    (hreq : Cedar.Validation.validateRequest ts req = .ok ()) :
    Cedar.Thm.InstanceOfWellFormedSchema ts req (entities ts pc mc store) := by
  simp only [Cedar.Validation.validateRequest] at hreq
  split at hreq
  · rename_i hany
    simp only [List.any_eq_true] at hany
    obtain ⟨env, henv, hmatch⟩ := hany
    refine ⟨env, henv, ?_, ?_, ?_⟩
    · simp only [Cedar.Validation.Schema.validateWellFormed] at hwf
      exact Cedar.Thm.env_validate_well_formed_is_sound (List.forM_ok_implies_all_ok _ _ hwf env henv)
    · exact Cedar.Thm.instance_of_request_type_refl hmatch
    · simp only [Cedar.Validation.Schema.environments, List.mem_map] at henv
      obtain ⟨rty, _, rfl⟩ := henv
      exact instanceOfSchema_entities ts pc mc _ store rfl rfl
  · cases hreq

/-! ## 一致の定理 -/

/-- 限定した判定材料(要求に現れる実体から `level` 段で到達できる実体だけ)での Cedar の判定は、判定の実体全体
    での判定と一致する。前提は、型環境が well-formed、要求がある環境のインスタンス、ポリシーが `level` で
    cedar-lean の level 検証に通ること(いずれも実行可能な検査の成功)。証明は cedar-lean の slicing 定理に委ね、
    評価器の中身には触れない。 -/
theorem isAuthorized_slice (ts : Cedar.Validation.Schema) (pc : ParentColumns) (mc : MembershipColumns)
    (policies : Policies) (store : Store) (req : Request) (level : Nat)
    (hwf : ts.validateWellFormed = .ok ())
    (hreq : Cedar.Validation.validateRequest ts req = .ok ())
    (hlevel : Cedar.Validation.validateWithLevel policies ts level = .ok ()) :
    isAuthorized req ((entities ts pc mc store).sliceAtLevel req level) policies
      = isAuthorized req (entities ts pc mc store) policies :=
  (Cedar.Thm.validate_with_level_is_sound_wf (instanceOfWellFormedSchema ts pc mc store req hwf hreq) hlevel).symm

/-! ## 部分的な取得 -/

/-- 実 DB から部分的に取得した判定材料: 取得できた行(`rows`)、引いたが無かった実体(`absent`)、そして絞り込みに
    合う行をすべて取得したテーブルと絞り込み(`fetched`。所属行の取得の記録)。接続層はこれを主キーの点検索と
    WHERE 句つきの SELECT(一覧の対象テーブル・制約の判定が見る行・所属行)で組み立てる。 -/
structure Known where
  rows : Store
  absent : List EntityUID
  fetched : List (Table × List Filter)

/-- 実体 `uid` の行の有無が分かっているか: 行を取得済みか、無いと分かっている。 -/
def Known.decided (k : Known) (uid : EntityUID) : Bool :=
  (Map.find? k.rows uid).isSome || k.absent.contains uid

/-- 実体 `uid` の所属行(型の各宣言について、所属する側の列が `uid` である行)をすべて取得したと記録しているか。
    所属行の宣言が無い型では真。 -/
def Known.coversMemberships (mc : MembershipColumns) (k : Known) (uid : EntityUID) : Bool :=
  ((mc.lookup uid.ty).getD []).all fun m => k.fetched.contains (m.table, m.filterOf uid)

/-- 実体 `uid` について部分的な取得が答えを持っているか: 型環境のテーブルでない型(匿名・アクション等。
    行の実体にならない)か、行の有無が分かっていてその所属行を取得済みである。 -/
def Known.knows (ts : Cedar.Validation.Schema) (mc : MembershipColumns) (k : Known) (uid : EntityUID) : Bool :=
  !(ts.ets.find? uid.ty).isSome || (k.decided uid && k.coversMemberships mc uid)

/-- 部分的な取得が全体の状態 `full` と整合すること: 取得した行は `full` のその行であり、無いと分かった実体は
    `full` にも無く、すべて取得したと記録した絞り込みについては、絞り込みに合う行が全体と集合として同じ。
    接続層ではこれが「点検索(絞り込みでは WHERE 句つきの SELECT)の結果は DB の現在の行である」という信頼
    (`ASSUMPTIONS.md` Assumption 1)に当たる。 -/
def Known.Consistent (k : Known) (full : Store) : Prop :=
  (∀ uid row, Map.find? k.rows uid = some row → Map.find? full uid = some row) ∧
  (∀ uid ∈ k.absent, Map.find? full uid = none) ∧
  (∀ tf ∈ k.fetched, RowsAgree k.rows full tf.1 tf.2)

/-- 整合する部分的な取得は、行の有無が分かっている UID について全体と同じ `find?` を返す。 -/
theorem Known.find?_eq_of_decided {k : Known} {full : Store} (hc : k.Consistent full) {uid : EntityUID}
    (hd : k.decided uid = true) : Map.find? k.rows uid = Map.find? full uid := by
  simp only [Known.decided, Bool.or_eq_true, List.contains_iff_mem] at hd
  rcases hd with hsome | habs
  · cases hr : Map.find? k.rows uid with
    | none => rw [hr] at hsome; cases hsome
    | some row => exact (hc.1 uid row hr).symm
  · have hnone := hc.2.1 uid habs
    cases hr : Map.find? k.rows uid with
    | none => rw [hnone]
    | some row => rw [hc.1 uid row hr] at hnone; cases hnone

/-- 整合する部分的な取得は、答えを持つテーブルの UID について全体と同じ `find?` を返す。 -/
theorem Known.find?_eq_of_knows {ts : Cedar.Validation.Schema} {mc : MembershipColumns} {k : Known} {full : Store}
    (hc : k.Consistent full) {uid : EntityUID}
    (hk : k.knows ts mc uid = true) (htable : (ts.ets.find? uid.ty).isSome = true) :
    Map.find? k.rows uid = Map.find? full uid := by
  simp only [Known.knows, Bool.or_eq_true, Bool.and_eq_true] at hk
  rcases hk with hno | ⟨hd, _⟩
  · simp only [Bool.not_eq_true'] at hno
    rw [hno] at htable
    cases htable
  · exact Known.find?_eq_of_decided hc hd

/-- 整合する部分的な取得は、答えを持つテーブルの UID について、その所属行が全体と集合として同じ。 -/
theorem Known.memberships_eq_of_knows {ts : Cedar.Validation.Schema} {mc : MembershipColumns} {k : Known}
    {full : Store} (hc : k.Consistent full) {uid : EntityUID}
    (hk : k.knows ts mc uid = true) (htable : (ts.ets.find? uid.ty).isSome = true) :
    ∀ m ∈ (mc.lookup uid.ty).getD [], RowsAgree k.rows full m.table (m.filterOf uid) := by
  simp only [Known.knows, Bool.or_eq_true, Bool.and_eq_true] at hk
  rcases hk with hno | ⟨_, hm⟩
  · simp only [Bool.not_eq_true'] at hno
    rw [hno] at htable
    cases htable
  · intro m hmem
    simp only [Known.coversMemberships, List.all_eq_true, List.contains_iff_mem] at hm
    exact hc.2.2 _ (hm m hmem)

/-- 閉包の検査(実行可能): 判定の実体 `es` について、要求から `level` 段で到達できる実体(cedar-lean の slicing
    が辿る集合 `Entities.sliceAtLevel.sliceAtLevel`)がすべて `knows` を満たす。 -/
def closedAt (es : Entities) (knows : EntityUID → Bool) (req : Request) (level : Nat) : Bool :=
  (Entities.sliceAtLevel.sliceAtLevel es req.sliceEUIDs level).all knows

private theorem filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a List.mem_cons_self]
    rw [filterMap_congr fun x hx => h x (List.mem_cons_of_mem a hx)]

/-- 要求から到達できる実体の集合は、その集合の各実体で `find?` が一致する 2 つの判定の実体について等しい。 -/
theorem reach_eq (e₁ e₂ : Entities) (work : Set EntityUID) :
    ∀ n, (∀ u ∈ Entities.sliceAtLevel.sliceAtLevel e₁ work n, e₁.find? u = e₂.find? u) →
      Entities.sliceAtLevel.sliceAtLevel e₁ work n = Entities.sliceAtLevel.sliceAtLevel e₂ work n
  | 0, _ => by simp only [Entities.sliceAtLevel.sliceAtLevel]
  | n + 1, h => by
    have hwork : ∀ u ∈ work, e₁.find? u = e₂.find? u :=
      fun u hu => h u (Cedar.Thm.in_work_then_in_slice hu)
    have heds : work.elts.filterMap e₁.find? = work.elts.filterMap e₂.find? :=
      filterMap_congr fun u hu => hwork u ((Set.mem_elts_iff_mem_set u work).mp hu)
    simp only [Entities.sliceAtLevel.sliceAtLevel]
    rw [heds]
    congr 1
    apply List.mapUnion_congr
    intro ed hed
    apply reach_eq e₁ e₂ ed.sliceEUIDs n
    intro u hu
    apply h u
    simp only [Entities.sliceAtLevel.sliceAtLevel]
    rw [Set.mem_union]
    right
    rw [← heds] at hed
    exact List.mem_mem_implies_mem_mapUnion hu hed

/-- 限定した判定材料(slice)は、到達できる各実体で `find?` が一致する 2 つの判定の実体について等しい。 -/
theorem sliceAtLevel_eq (e₁ e₂ : Entities) (req : Request) (level : Nat)
    (h : ∀ u ∈ Entities.sliceAtLevel.sliceAtLevel e₁ req.sliceEUIDs level, e₁.find? u = e₂.find? u) :
    e₁.sliceAtLevel req level = e₂.sliceAtLevel req level := by
  simp only [Entities.sliceAtLevel]
  rw [reach_eq e₁ e₂ req.sliceEUIDs level h]
  congr 1
  apply filterMap_congr
  intro u hu
  rw [h u (by rw [reach_eq e₁ e₂ req.sliceEUIDs level h]; exact (Set.mem_elts_iff_mem_set u _).mp hu)]

/-- 閉包の検査に通れば、到達できる各実体は `knows` を満たす。 -/
theorem closedAt_spec {es : Entities} {knows : EntityUID → Bool} {req : Request} {level : Nat}
    (h : closedAt es knows req level = true) :
    ∀ u ∈ Entities.sliceAtLevel.sliceAtLevel es req.sliceEUIDs level, knows u = true :=
  Set.all_eq_true.mp h

end Nyxis.Materials

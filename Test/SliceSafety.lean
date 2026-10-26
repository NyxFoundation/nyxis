import Test.Materials
import Nyxis.SliceSafety

/-!
# Test.SliceSafety — 判定材料による応答の決定(`Nyxis.SliceSafety`)の実例

`Test.Materials` の検査用正本と状態 `store` に、alice の非公開の文書 `secret`(共有先なし)を足した状態 `store₂` を
並べ、次を `#guard` で確かめる(`lake build` で実行される):

- 1 回の呼び出しで、両方の状態と整合し判定材料を覆う部分的な取得があるとき(`SliceAgree` の実行可能な版)、
  結果(許可も拒否も)と発行が 2 つの状態で一致すること(`step_eq_of_slice` の実例。前提が空虚でないこと)。
- 2 回の呼び出しのハンドラで、各呼び出しの判定材料が一致し、HTTP モデル応答が一致すること
  (`handleRequest_eq_of_agree` の実例)。
- 判定材料が異なれば結果は異なりうること: 所有者 alice の一覧は件数で `secret` の有無を区別し、そのとき一覧の
  判定材料(対象テーブルの絞り込みに合う行)は 2 つの状態で一致しない。
-/

namespace Test.SliceSafety

open Cedar.Spec
open Cedar.Data
open Nyxis
open Nyxis.Db
open Nyxis.Authz
open Test.Materials

/-- `store` に、alice の非公開の文書 `secret` を足した状態。 -/
def store₂ : Store := Map.make
  [ (alice, userRow false), (bob, userRow false), (carol, userRow true)
  , (doc "pub", docRow alice [bob] ["public"] carol true)
  , (doc "priv", docRow alice [bob] ["team"] carol false)
  , (doc "secret", docRow alice [] ["team"] alice false) ]

/-- `Known.Consistent` の実行可能な版(絞り込みの記録が無い取得について)。 -/
def consistentB (k : Nyxis.Materials.Known) (s : Store) : Bool :=
  k.rows.toList.all (fun kv => Map.find? s kv.1 == some kv.2) &&
    k.absent.all (fun u => (Map.find? s u).isNone) && k.fetched.isEmpty

/-- `SliceSafety.SliceAgree` の実行可能な版: 取得 `k` が両方の状態と整合し、判定材料を覆い、判定が絞り込みで見る行が
    両方の状態と一致する。 -/
def sliceAgreesB (k : Nyxis.Materials.Known) (p : Principal) (action : String) (key : Key)
    (values : Row := Map.empty) : Bool :=
  consistentB k store && consistentB k store₂ &&
    coversStep schema policies k p gen (act action) key values {} &&
    (rowFilters schema k.rows (act action) key values {}).all fun tf =>
      matchingRows k.rows tf.1 tf.2 == matchingRows store tf.1 tf.2 &&
        matchingRows k.rows tf.1 tf.2 == matchingRows store₂ tf.1 tf.2

/-- 2 つの状態での `step` の結果と発行(状態を除く)が一致する。 -/
def stepSame (p : Principal) (action : String) (key : Key) (values : Row := Map.empty) : Bool :=
  let s₁ := step schema policies p gen store (act action) key values {}
  let s₂ := step schema policies p gen store₂ (act action) key values {}
  s₁.outcome == s₂.outcome &&
    s₁.issued.map (fun i => (i.action, i.op)) == s₂.issued.map (fun i => (i.action, i.op))

-- 判定材料が一致する呼び出し: 結果は一致する(`secret` は見えない)
#guard sliceAgreesB (known [carol, doc "pub"]) (.user carol) "readDoc" "pub"
#guard stepSame (.user carol) "readDoc" "pub"
#guard (step schema policies (.user carol) gen store₂ (act "readDoc") "pub" Map.empty {}).outcome
  == .ok (Map.find? store (doc "pub"))
#guard sliceAgreesB (known [bob, doc "priv"]) (.user bob) "readDoc" "priv"
#guard stepSame (.user bob) "readDoc" "priv"
-- 拒否も一致する
#guard sliceAgreesB (known [carol, doc "priv"]) (.user carol) "readDoc" "priv"
#guard stepSame (.user carol) "readDoc" "priv"
#guard (step schema policies (.user carol) gen store₂ (act "readDoc") "priv" Map.empty {}).outcome == .denied
-- 書き込みも一致する(判定材料は主体と対象の行)
#guard sliceAgreesB (known [bob, doc "pub"]) (.user bob) "editDoc" "pub" (row [("labels", setV [strV "x"])])
#guard stepSame (.user bob) "editDoc" "pub" (row [("labels", setV [strV "x"])])

/-- carol が `pub` を読み、続けて `priv` を読む 2 回の呼び出しのハンドラ。応答は 2 つの結果のタグ。 -/
def twoReads : Handler Http.Response := do
  let o₁ ← Handler.callAction (act "readDoc") "pub"
  let o₂ ← Handler.callAction (act "readDoc") "priv"
  let tag : Outcome → String := fun
    | .ok _ => "ok" | .denied => "denied" | _ => "other"
  pure { status := .ok, body := tag o₁ ++ "," ++ tag o₂ }

def runOn (s : Store) : Runtime.Run Http.Response :=
  Runtime.runHandler schema policies (.user carol) gen s [] twoReads

-- 各呼び出しの判定材料が一致する(読み取りは状態を変えないので、2 回目も同じ 2 つの状態で判定する)
#guard (runOn store).result.body == "ok,denied"
#guard (runOn store).result.body == (runOn store₂).result.body
#guard (runOn store).result.status == (runOn store₂).result.status

-- 判定材料が異なれば結果は異なりうる: 一覧の判定材料は対象テーブルの絞り込みに合う全行で、`secret` を含むかで
-- 2 つの状態は一致せず、所有者 alice の一覧の件数は異なる
#guard !sliceAgreesB (known [alice, doc "pub", doc "priv", doc "secret"]) (.user alice) "listDocs" ""
#guard !stepSame (.user alice) "listDocs" ""

end Test.SliceSafety

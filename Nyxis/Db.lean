import Cedar.Spec
import Cedar.Validation

/-!
# Nyxis.Db — the DB layer

Defines the DB operations the Lean backend issues to PostgreSQL, the declarations of "effects" attached to actions, and
a pure model of the DB state (`Store`).

- Tables correspond one-to-one to Cedar entity types, columns to attributes, and primary keys to entity IDs. There is no
  mapping code; Cedar's types are used as they are.
- Each action has exactly one effect. It fixes the kind (read, list, insert, update, delete, and the declared external
  effects — issuing signed URLs for attachments `upload` / `download`, sending mail `mail`, and external API calls
  `call`) and the target table; for updates the columns, for mail the recipient column and the subject and body columns,
  and for external API calls the destination, method, path (or URL column), body columns, and execution timing. A list
  runs that action's decision for each row of the target table and returns only the permitted rows. As DB operations, it
  issues one read per permitted row (`Nyxis.Authz.step`). External effects issue no DB operations; only when permitted
  for the target row do they record the external effect (issuing a signed URL to Supabase Storage, sending mail whose
  recipient and content are the values of that row's declared columns, or an HTTP call to a destination declared in the
  approved schema) (`Nyxis.Authz.External`). nyxis decides the object path (`objectPath`); the recipient, content,
  destination, and body are determined by the approved schema's declaration and the row's declared columns (for calls,
  also the proposed values in `context.values`), and the handler cannot name them.
- DB operations are issued by the authorization layer (`Nyxis.Authz`) only on permit. Handlers do not touch this layer.
- `Store` is a pure model abstracting the contents of PostgreSQL, and the authorization safety theorem (`Nyxis.Runtime`)
  is stated over it. That the DB changes only through operations nyxis issues (that the DB is reachable only by the
  dedicated nyxis role) and that the runtime conveying operations to PostgreSQL is correct are trusted outside the proof
  (`ASSUMPTIONS.md`).
-/

namespace Nyxis

open Cedar.Spec

namespace Db

/-- A table name. Corresponds one-to-one to a Cedar entity type. -/
abbrev Table := EntityType

/-- A column name. Corresponds one-to-one to a Cedar attribute. -/
abbrev Column := Attr

/-- A row's primary key. Corresponds one-to-one to a Cedar entity ID. -/
abbrev Key := String

/-- A column value. Cedar values are used as they are. -/
abbrev Cell := Value

/-- A row's contents. A map from column names to values. -/
abbrev Row := Cedar.Data.Map Column Cell

/-- Overlays changes on a row. Columns in the changes get the new value; other columns keep the original value. -/
def Row.patch (row changes : Row) : Row :=
  Cedar.Data.Map.make (changes.toList ++ row.toList.filter (fun kv => !changes.contains kv.1))

/-! ## Declaring external API calls

The approved schema declares named destinations (reserved companions with `@external` attached, such as
`entity Stripe;`; not tables) and declares calls with the effect
`@effect("call <destination> <method> <path | url: column> T(column, …) (sync [<seconds>s] -> <record type> | async)")`.
A destination has a base URL (`base`; without one, the value of a String column of the target row becomes the
destination via `url: column` — the former Webhook form) and an authentication method (only the environment variable
name appears in the approved schema; the value is a core setting). Handlers can assemble neither URLs nor headers. -/

/-- A call's HTTP method. -/
inductive CallMethod where
  | get
  | post
  | put
  | patch
  | delete
  deriving Repr, DecidableEq

/-- The name in HTTP. -/
def CallMethod.name : CallMethod → String
  | .get => "GET"
  | .post => "POST"
  | .put => "PUT"
  | .patch => "PATCH"
  | .delete => "DELETE"

/-- Whether the method sends a body (`GET` / `DELETE` send none). -/
def CallMethod.hasBody : CallMethod → Bool
  | .get | .delete => false
  | .post | .put | .patch => true

/-- A destination's authentication method. Only the environment variable name appears in the approved schema; the value
    is passed as a core setting (`NYXIS_EXT_<name>`). -/
inductive DestinationAuth where
  /-- No authentication header. -/
  | none
  /-- `Authorization: Bearer <value of the environment variable>`. -/
  | bearer (env : String)
  /-- One arbitrary header `<name>: <value of the environment variable>`. -/
  | header (name env : String)
  deriving Repr, DecidableEq

/-- A named destination (`@external`). `base` is a fixed base URL starting with `https://` (with no trailing `/`). A
    destination without `base` can only be used by `url: column` calls. -/
structure Destination where
  base : Option String
  auth : DestinationAuth
  deriving Repr, DecidableEq

/-- How a call's destination is determined. -/
inductive CallTarget where
  /-- A fixed path appended to the destination's base URL. Only `{key}` is filled with the target row's primary key. -/
  | path (path : String)
  /-- Uses the value of a String column of the target row (one starting with `https://`) as the URL (`url: column`). The
      destination has no `base`. -/
  | column (url : Column)
  deriving Repr, DecidableEq

/-- Execution timing. `sync` sends synchronously within the request's transaction and decodes the response into the
    record type declared in the approved schema before passing it to the handler (`timeout` overrides the limit on the
    whole transfer, in seconds). `async` writes to the outbox (`_nyxis_outbox`) with no response, and nyxis's internal
    loop sends it after the COMMIT. -/
inductive CallMode where
  | sync (timeout : Option Nat) (response : Cedar.Validation.CedarType)
  | async
  deriving Repr, DecidableEq

/-- The kind of an action's effect. For updates it fixes the columns that may be changed. A list (`list`) runs that
    action's decision for each row of the target table and returns only the permitted rows. `upload` / `download` issue
    a signed upload / download URL for an attachment of the target row; they are declared external effects that do not
    change the DB. nyxis decides the object path with `objectPath` (`table/<primary key>/<generated ID>`; for downloads,
    the value of the column the approved schema names with `@attachment("column")`). `mail` sends mail whose recipient
    (`recipient`; a String column holding an email address) and content (`content`: the first is the subject and the
    rest are body paragraphs; String columns) are the values of the target row's declared columns. `call` is an HTTP
    call to the destination `destination` declared in the approved schema: the method, how the destination is determined
    (a fixed path appended to the base URL, or the target row's URL column), the target row's columns `columns` put in
    the body, whether the proposed values in `context.values` are also mixed into the body and placed in the decision
    context (`proposes`; when the action's `context` in the approved schema declares `values`), and the execution timing
    `mode`. All of these are declared external effects that do not change the DB; the recipient, content, destination,
    and body are all determined by the approved schema's declaration and the row's columns (and the proposed values that
    passed the decision), and the handler cannot choose them. -/
inductive EffectKind where
  | read
  | list
  | insert
  | update (columns : List Column)
  | delete
  | upload
  | download
  | mail (recipient : Column) (content : List Column)
  | call (destination : String) (method : CallMethod) (target : CallTarget) (columns : List Column) (proposes : Bool)
      (mode : CallMode)
  deriving Repr, DecidableEq

/-- Whether the kind is a declared external effect. -/
def EffectKind.isExternal : EffectKind → Bool
  | .upload | .download | .mail _ _ | .call .. => true
  | .read | .list | .insert | .update _ | .delete => false

/-- The effect declaration attached to an action. Exactly one per action. -/
structure Effect where
  kind : EffectKind
  table : Table
  deriving Repr, DecidableEq

/-- A DB operation: the reads, inserts, updates, and deletes the Lean backend issues to PostgreSQL. A list is issued as
    one read per permitted row (there is no list-only operation). -/
inductive Operation where
  | read (table : Table) (key : Key)
  | insert (table : Table) (key : Key) (row : Row)
  | update (table : Table) (key : Key) (changes : Row)
  | delete (table : Table) (key : Key)

/-- The operation's target (table and primary key). Becomes Cedar's target entity UID. -/
def Operation.target : Operation → EntityUID
  | .read t k | .insert t k _ | .update t k _ | .delete t k => ⟨t, k⟩

/-- The values the operation proposes: the whole row for inserts, the changed columns for updates, none for reads and
    deletes. -/
def Operation.proposed : Operation → Option Row
  | .insert _ _ row => some row
  | .update _ _ changes => some changes
  | .read _ _ | .delete _ _ => none

/-- Builds, from the effect declaration, the DB operation for primary key `key` and proposed values `values`. The effect
    fixes the operation's kind and table; the handler cannot choose them. List effects are handled per row beforehand by
    `Nyxis.Authz.step` (for each row's primary key, a read of that row), so the `.list` branch here is never reached. It
    exists to make the function total. For external effects, this operation is used only to build the decision materials
    (principal, target row, context) and is not issued as a DB operation (`Nyxis.Authz.externalStep`): the decision
    materials are the same as for a read of the target row, and for calls that take the proposed values in
    `context.values` (`proposes` of `call`) it is built in the update form (target row and proposed values) so that the
    proposed values are placed in the context. -/
def Operation.ofEffect (e : Effect) (key : Key) (values : Row) : Operation :=
  match e.kind with
  | .read => .read e.table key
  | .list => .read e.table key
  | .insert => .insert e.table key values
  | .update _ => .update e.table key values
  | .delete => .delete e.table key
  | .upload => .read e.table key
  | .download => .read e.table key
  | .mail _ _ => .read e.table key
  | .call _ _ _ _ proposes _ => if proposes then .update e.table key values else .read e.table key

/-- Whether the DB operation is within the scope of the effect declaration: the kind and table match, and for updates
    the changed columns fall within the declared columns. Within the scope of a list effect are only reads of that
    table's rows. -/
def Operation.withinEffect (op : Operation) (e : Effect) : Bool :=
  match op, e.kind with
  | .read t _, .read => t == e.table
  | .read t _, .list => t == e.table
  | .insert t _ _, .insert => t == e.table
  | .update t _ changes, .update cols =>
    t == e.table && changes.toList.all (fun kv => cols.contains kv.1)
  | .delete t _, .delete => t == e.table
  | _, _ => false

/-! ## Attachment object paths

The path of the Supabase Storage object targeted by a signed URL is decided by nyxis in the form
`table/<primary key>/<object name>`. The object name is, for uploads, the unique ID of the request's server-generated
values, and for downloads, the current value of the String column that the approved schema names with
`@attachment("column")`. Both the primary key and the name must consist only of alphanumerics, `-`, and `_` (1-128
characters; no path separators or `..`); otherwise no path is determined (the handler gets `Outcome.notFound`). Handlers
can name neither the path nor the bucket. -/

/-- Whether the string can be used as an element of an object path (ASCII alphanumerics, `-`, `_`; 1-128 characters). -/
def isObjectToken (s : String) : Bool :=
  s.length > 0 && s.length ≤ 128 &&
    s.toList.all fun c => c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_')

/-- The object path `table/<primary key>/<name>`. `none` if the primary key or name cannot be used as an element. -/
def objectPath (table : Table) (key : Key) (token : String) : Option String :=
  if isObjectToken key && isObjectToken token then some (table.id ++ "/" ++ key ++ "/" ++ token) else none

/-! ## External API call URLs

The destination URL is either the base URL (`base` of `@external` in the approved schema) followed by the fixed path
written in the approved schema, or the value of a String column of the target row (`url: column`). Only `{key}` in the
path is filled with the target row's primary key, and the primary key must be a string usable as a path element
(`isObjectToken`). The value of a `url: column` must be printable ASCII starting with `https://`. If neither is
determined, the call's content is not determined (the handler gets `Outcome.notFound`). -/

/-- Whether the string can be used as a destination URL: it starts with `https://`, is printable ASCII, and contains
    none of `"`, `\`, `#`, or whitespace (up to 2048 characters). -/
def isHttpsUrl (url : String) : Bool :=
  url.startsWith "https://" && url.length > 8 && url.length ≤ 2048 &&
    url.toList.all fun c => 33 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\' && c != '#'

/-- Fills `{key}` in the path with the primary key. If `{key}` is present, the primary key must be a string usable as a
    path element (otherwise `none`). There is no other substitution (the approved schema check rejects placeholders
    other than `{key}`). -/
def fillPath (path : String) (key : Key) : Option String :=
  match path.splitOn "{key}" with
  | [_] => some path
  | parts => if isObjectToken key then some (key.intercalate parts) else none

/-- The call's URL: for a fixed path, the destination's base URL followed by the filled path; for `url: column`, the
    value of that column of the target row (only if `isHttpsUrl`). `none` if the destination's form and the
    declaration's form do not match (the approved schema check rejects this, so it never arises from the approved
    schema). -/
def callUrl (destination : Destination) (target : CallTarget) (key : Key) (row : Row) : Option String :=
  match target, destination.base with
  | .path p, some base => (fillPath p key).map (base ++ ·)
  | .column c, none =>
    match row.find? c with
    | some (.prim (.string url)) => if isHttpsUrl url then some url else none
    | _ => none
  | .path _, none | .column _, some _ => none

/-! ## List queries

For a list, a handler can specify filters comparing column values with constants (equality, ordering), sorting, and a
page (position and limit). Filtering happens before the decision (in the real DB, in the SELECT's WHERE clause); sorting
and paging apply to the permitted rows. The count (`total` of `Outcome.list`) is the number of rows that match the
filters and are permitted, before paging. -/

/-- A filter comparison. -/
inductive Comparison where
  | eq
  | lt
  | le
  | gt
  | ge
  deriving Repr, DecidableEq

/-- Whether the comparison accepts the ordering (`lt` only `.lt`, `le` `.lt` and `.eq`, …). -/
def Comparison.accepts : Comparison → Ordering → Bool
  | .eq, .eq | .lt, .lt | .le, .lt | .le, .eq | .gt, .gt | .ge, .gt | .ge, .eq => true
  | _, _ => false

/-- A list filter: a comparison of the value of column `column` with constant `value`. -/
structure Filter where
  column : Column
  comparison : Comparison
  value : Cell
  deriving Repr, DecidableEq

/-- The sort direction. -/
inductive Direction where
  | asc
  | desc
  deriving Repr, DecidableEq

/-- One sort key: a column and a direction. -/
structure OrderBy where
  column : Column
  direction : Direction := .asc
  deriving Repr

/-- The query a handler specifies for a list. Filters select rows that satisfy all conditions (AND); sorting proceeds
    from the first key (the next key on ties, primary key order if all are equal); the page is `limit` rows (to the end
    if `none`) starting at position `offset` of the sorted sequence of permitted rows. -/
structure ListQuery where
  filters : List Filter := []
  orderBy : List OrderBy := []
  offset : Nat := 0
  limit : Option Nat := none
  deriving Repr

/-- The ordering of scalar values. Only integers, strings, booleans, datetimes, durations, and decimals of the same kind
    are compared; values of different kinds, sets, and records cannot be compared (`none`). Strings are in code point
    order (the same as the "C" collation in the real DB). -/
def Cell.compare? : Cell → Cell → Option Ordering
  | .prim (.int a), .prim (.int b) => some (compareOfLessAndEq a b)
  | .prim (.string a), .prim (.string b) => some (compareOfLessAndEq a b)
  | .prim (.bool a), .prim (.bool b) => some (compareOfLessAndEq a b)
  | .ext (.datetime a), .ext (.datetime b) => some (compareOfLessAndEq a.val b.val)
  | .ext (.duration a), .ext (.duration b) => some (compareOfLessAndEq a.val b.val)
  | .ext (.decimal a), .ext (.decimal b) => some (compareOfLessAndEq a b)
  | _, _ => none

/-- Whether the row matches the filter. It does not match if the column is missing. Equality is equality of the values
    themselves; ordering uses the order of `Cell.compare?` (no match if they cannot be compared). -/
def Filter.matches (f : Filter) (row : Row) : Bool :=
  match row.find? f.column with
  | none => false
  | some v =>
    match f.comparison with
    | .eq => v == f.value
    | c =>
      match Cell.compare? v f.value with
      | some o => c.accepts o
      | none => false

/-- Whether the row matches all filters. -/
def ListQuery.matches (q : ListQuery) (row : Row) : Bool :=
  q.filters.all (·.matches row)

/-- Compares two rows by one sort key. Rows missing the column come first. Values that cannot be compared are treated as
    equal. -/
def OrderBy.compare (o : OrderBy) (a b : Row) : Ordering :=
  let r := match a.find? o.column, b.find? o.column with
    | some x, some y => (Cell.compare? x y).getD .eq
    | some _, none => .gt
    | none, some _ => .lt
    | none, none => .eq
  match o.direction with
  | .asc => r
  | .desc => r.swap

/-- The sort order (`a` comes before `b` or ties with it). Primary key order if equal on every key. -/
def ListQuery.le (q : ListQuery) (a b : Key × Row) : Bool :=
  go q.orderBy
where
  go : List OrderBy → Bool
    | [] => decide (a.1 < b.1) || a.1 == b.1
    | o :: rest =>
      match o.compare a.2 b.2 with
      | .lt => true
      | .gt => false
      | .eq => go rest

/-- Selects the rows to return from the sequence of permitted rows: sorts them (`List.mergeSort`; stable) and takes
    `limit` rows starting at position `offset`. -/
def ListQuery.select (q : ListQuery) (rows : List (Key × Row)) : List (Key × Row) :=
  let sorted := rows.mergeSort q.le
  (sorted.drop q.offset).take (q.limit.getD sorted.length)

/-- Every returned row is in the sequence before selection (sorting and paging do not add rows). -/
theorem ListQuery.mem_select (q : ListQuery) (rows : List (Key × Row)) (kv : Key × Row)
    (h : kv ∈ q.select rows) : kv ∈ rows :=
  List.mem_mergeSort.mp (List.mem_of_mem_drop (List.mem_of_mem_take h))

/-- Whether the row matches all filters (the same rule as `ListQuery.matches`; determined only by the filter columns).
    -/
def Filter.matchesAll (filters : List Filter) (row : Row) : Bool :=
  filters.all (·.matches row)

/-! ## Uniqueness and referential integrity declarations

DB constraints declared by the approved schema. `@unique("column, …")` is uniqueness of a column tuple (rows missing any
of the tuple's columns are not compared; the same as NULL under PostgreSQL's `UNIQUE`), and
`@references("column restrict, column cascade action, …")` is referential integrity of entity reference columns (an
insert or update whose referenced row does not exist is a conflict; deleting a referenced row is a conflict under
`restrict` if referencing rows exist, and under `cascade` also deletes the referencing rows — each of them is decided by
a declared action with that table's delete effect, and if even one row is not permitted, the whole request is rejected).
nyxis also sets the same constraints in the DB (`PostgresSql.createTable`), and the model (`Nyxis.Authz.step`) decides
first (a violation is `Outcome.conflict`). The DB-side constraints are a backstop for when the decision is wrong, in
which case the whole request is closed. -/

/-- A uniqueness declaration for a column tuple. -/
structure Unique where
  table : Table
  columns : List Column
  deriving Repr, DecidableEq

/-- The behavior when deleting a referenced row. `cascade` carries the action that decides the referencing rows (that
    table's delete effect). -/
inductive OnDelete where
  | restrict
  | cascade (action : EntityUID)
  deriving Repr, DecidableEq

/-- A referential integrity declaration for an entity reference column: the referencing table and column, the referenced
    table, and the behavior on delete. -/
structure Reference where
  table : Table
  column : Column
  target : Table
  onDelete : OnDelete
  deriving Repr, DecidableEq

/-- The constraints the schema declares. -/
structure Constraints where
  uniques : List Unique := []
  references : List Reference := []
  deriving Repr, DecidableEq

/-- The filters for a uniqueness tuple: equality with the values of row `new`'s columns. Not compared (`none`) if `new`
    lacks even one of the tuple's columns. -/
def Unique.filtersOf (u : Unique) (new : Row) : Option (List Filter) :=
  u.columns.mapM fun c => (new.find? c).map fun v => ⟨c, .eq, v⟩

/-- The filter for rows that reference entity `uid` through column `column`. -/
def Reference.filterOf (column : Column) (uid : EntityUID) : List Filter :=
  [⟨column, .eq, .prim (.entityUID uid)⟩]

end Db

/-- The result of an action call. `denied` is decided by the authorization layer; `notFound` / `conflict` / `ok` by the
    DB layer. -/
inductive Outcome where
  /-- The authorization layer rejected it (no effect declaration, the operation is outside the effect's scope, or Cedar
      denies). No DB operation has been issued. -/
  | denied
  /-- The row does not exist (read, update, delete). -/
  | notFound
  /-- The row already exists (insert). -/
  | conflict
  /-- Success. For reads, that row; for writes (insert, update, delete), `none`. Returning a row from a write effect
      would be a read beyond the declared effect (for updates, the columns), so none is returned. -/
  | ok (row : Option Db.Row)
  /-- A successful list. Returns, with their primary keys, the rows of the target table that match the filters and for
      which the action is permitted to the principal (`total` is their number), sorted and paged. -/
  | list (rows : List (Db.Key × Db.Row)) (total : Nat)
  /-- A successful external effect (issuing a signed URL for an attachment). The signed URL issued by Supabase Storage.
      No row is passed. In the pure model this value is an arbitrary string from the request's sequence of external
      effect results (`Nyxis.Runtime.Externals`), and the theorem states that the record of its issuance
      (`Nyxis.Authz.External`) is authorized (items (6)(7) of the main theorem). Successful mail sends and `async` calls
      are `ok none` (the send's result has no value and does not change the DB). -/
  | signed (url : String)
  /-- The value obtained by decoding the 2xx response of a `sync` external API call into the record type declared in the
      approved schema (rejecting only missing declared keys and type mismatches, and discarding extra keys). No row is
      passed. In the pure model this value is an arbitrary value from the request's sequence of external effect results,
      and the theorem states that the record of that call is authorized (items (6)(8) of the main theorem) and that the
      value derives from that call's record and does not change decisions ((9)). -/
  | called (value : Value)
  /-- A non-2xx response of a `sync` external API call. The status code and the raw body (the handler treats it as a
      business failure). -/
  | calledError (status : Nat) (body : String)

/-- The (primary key, row) pairs the result passes to the handler. For a successful read, the call's primary key `key`
    and that row; for a list, each returned pair; otherwise none. The theorem states where these pairs come from (item
    (3) of `Nyxis.Runtime.authorization_safety`). -/
def Outcome.entries (key : Db.Key) : Outcome → List (Db.Key × Db.Row)
  | .ok (some row) => [(key, row)]
  | .list rows _ => rows
  | .ok none | .denied | .notFound | .conflict | .signed _ | .called _ | .calledError _ _ => []

/-- Whether the result carries the value of an external effect's result (a signed URL, a call's response). Such results
    arise only from processing external effects (items (7)(9) of the main theorem). -/
def Outcome.isExternal : Outcome → Bool
  | .signed _ | .called _ | .calledError _ _ => true
  | .ok _ | .denied | .notFound | .conflict | .list _ _ => false

/-- Whether it is an external API call's response (`called` / `calledError`). -/
def Outcome.isCalled : Outcome → Bool
  | .called _ | .calledError _ _ => true
  | .ok _ | .denied | .notFound | .conflict | .list _ _ | .signed _ => false

namespace Db

/-- A pure model of the DB state. A finite map from (table, primary key) = entity UID to rows. -/
abbrev Store := Cedar.Data.Map EntityUID Row

namespace Store

/-- The row of table `table` with primary key `key`. -/
def find? (s : Store) (table : Table) (key : Key) : Option Row :=
  Cedar.Data.Map.find? s ⟨table, key⟩

/-- Puts a row. Replaces it if it already exists. -/
def put (s : Store) (table : Table) (key : Key) (row : Row) : Store :=
  Cedar.Data.Map.make
    (((⟨table, key⟩ : EntityUID), row) :: s.toList.filter (fun kv => kv.1 != (⟨table, key⟩ : EntityUID)))

/-- Removes a row. -/
def remove (s : Store) (table : Table) (key : Key) : Store :=
  Cedar.Data.Map.filter (fun uid _ => uid != (⟨table, key⟩ : EntityUID)) s

/-- All current rows of table `table` (primary keys and rows). The primary keys are taken in order from the rows in the
    current state, and each row is looked up with `find?` by that primary key (the same path as the read operation
    `apply (.read …)`). A list makes a decision for each of these rows. -/
def rows (s : Store) (table : Table) : List (Key × Row) :=
  (s.toList.filterMap fun kv => if kv.1.ty == table then some kv.1.eid else none).filterMap
    fun key => (s.find? table key).map (key, ·)

/-- Each row `rows` returns is the current row looked up with `find?` by its primary key. -/
theorem rows_find? (s : Store) (table : Table) (key : Key) (row : Row)
    (h : (key, row) ∈ s.rows table) : s.find? table key = some row := by
  simp only [rows, List.mem_filterMap] at h
  obtain ⟨k, _, hk⟩ := h
  cases hf : s.find? table k <;> simp only [hf, Option.map_none, Option.map_some, reduceCtorEq,
    Option.some.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  exact hf

/-- Applies a DB operation. Returns the new state and the result passed back to the handler. -/
def apply (s : Store) : Operation → Store × Outcome
  | .read t k =>
    match s.find? t k with
    | some row => (s, .ok (some row))
    | none => (s, .notFound)
  | .insert t k row =>
    match s.find? t k with
    | some _ => (s, .conflict)
    | none => (s.put t k row, .ok none)
  | .update t k changes =>
    match s.find? t k with
    | some row => (s.put t k (row.patch changes), .ok none)
    | none => (s, .notFound)
  | .delete t k =>
    match s.find? t k with
    | some _ => (s.remove t k, .ok none)
    | none => (s, .notFound)

/-- Reads do not change the DB state. -/
theorem apply_read_fst (s : Store) (table : Table) (key : Key) :
    (s.apply (.read table key)).1 = s := by
  simp only [apply]
  split <;> rfl

/-- The result of a row operation is not a list result (list results are produced by `Nyxis.Authz.step` only for list
    effects). -/
theorem apply_snd_ne_list (s : Store) (op : Operation) (rows : List (Key × Row)) (total : Nat) :
    (s.apply op).2 ≠ .list rows total := by
  cases op <;> simp only [apply] <;> split <;> simp

/-- The result of a row operation is not an external effect result (signed URLs and call responses are passed by
    `Nyxis.Authz.step` only for external effects). -/
theorem apply_snd_isExternal (s : Store) (op : Operation) :
    (s.apply op).2.isExternal = false := by
  cases op <;> simp only [apply] <;> split <;> rfl

/-- A result containing a row arises only from a primary key read on the same prior state: the row the result passes is
    the current row looked up with `find?` by that primary key, and the operation is a read. Values passed to writes and
    existing rows are never returned as results. -/
theorem apply_row (s : Store) (op : Operation) (row : Row)
    (h : (s.apply op).2 = .ok (some row)) :
    ∃ table key, op = .read table key ∧ s.find? table key = some row := by
  cases op <;> simp only [apply] at h
  all_goals split at h <;> simp_all
  exact ⟨_, _, ⟨rfl, rfl⟩, by assumption⟩

/-- A (primary key, row) pair the result passes arises only when the operation is a read; the primary key is the call's
    primary key passed to `entries`, and the row is the current row looked up with `find?` by that read's primary key
    (list results never arise from `apply`). -/
theorem apply_entries (s : Store) (op : Operation) (key : Key) (kv : Key × Row)
    (h : kv ∈ (s.apply op).2.entries key) :
    ∃ table readKey, op = .read table readKey ∧ kv.1 = key ∧ s.find? table readKey = some kv.2 := by
  cases op <;> simp only [apply] at h
  all_goals split at h <;> simp only [Outcome.entries, List.mem_singleton, List.not_mem_nil] at h
  subst h
  exact ⟨_, _, rfl, rfl, by assumption⟩

end Store

end Db

end Nyxis

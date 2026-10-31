# External API calls — design

The design of the mechanism for calling external HTTP APIs from the nyxis backend. It records the decisions finalized on 2026-10-25.

Related: [ASSUMPTIONS.md](../ASSUMPTIONS.md) Assumptions 2 and 3 (mail and external API destinations, keeping keys secret, and idempotency keys), [docs/proofs.md](proofs.md) (items (6)–(9) of the theorem),
[docs/connection.md](connection.md) 5. (sending external effects).

Implementation: the grammar of §3 and the rejections of §3.4 (`Nyxis/CedarSchema.lean`), the pure model (`EffectKind.call` in
`Nyxis/Db.lean`; `Payload.call` / `ExternalResult` / `CallRecorded` in `Nyxis/Authz.lean`), items (8) and (9) of the theorem
(`Nyxis/Runtime.lean`), sending `sync` calls and the lenient decoding of responses (`Nyxis/Internal/CallSend.lean`), mapping
decoding failures to a fixed 502 (`PostgresRun.handleStaged`: only `CallSend.invalidResponse` is mapped, after the rollback, to
`PostgresRun.gatewayResponse`), the integration test against a mock API (`Test/ExternalCalls.lean` and
`scripts/check-external-calls.py`), the outbox and internal loop of §4.2–§4.3 (`Nyxis/Internal/Outbox.lean`: `enqueue` writes
to `_nyxis_outbox` from `PostgresRun.driver` in the request's transaction, and `loop` / `tick` / `step` send one row at a time
with READ COMMITTED `FOR UPDATE SKIP LOCKED` and update its state. For the reserved table, `PostgresInit.plan` emits the DDL of
`PostgresSql.outbox` after the sources' tables. It is started by `Outbox.start` in `ApprovedServer.serve` (only when the
sources declare `async`). The integration tests are `Test/Outbox.lean` and `scripts/check-outbox.py`), and the adoption in the
second sample (in the sources of `examples/team-docs/backend`, the `@external` destinations `Summarizer` (`sync`; the handler
records the `summarizeDoc` response `{ summary: String }` into the column `summary` with a separate action `recordSummary` —
the policy rejects an empty summary) and `Audit` (`async`; `announceDocUpdate` after `editDoc` is sent via the outbox). The
destination is the local mock API `https://localhost:18118` (the sources' `base` is a fixed string, so the integration test
`scripts/check-team-docs.py` stands it up on the same fixed port). The startup code `Main.lean` wires up
`CallSend.Config.load` and `Outbox.Config.load`). The former `webhook` effect was removed as per D12
(`WebhookSend.lean` was deleted).

## 1. State and problems before implementation (as of the 2026-10-25 discussion)

Before implementation, `@effect("webhook T(URL column; body columns…)")` (the former `Nyxis/Internal/WebhookSend.lean`) was fixed as follows.

| Item | Current state |
|---|---|
| Method and format | POST, JSON only |
| Headers | Content-Type only (no authentication header can be added) |
| Destination | The value of a row's column. HTTPS only |
| Response | Only whether it is 2xx is checked; the body is discarded |
| Timing | Synchronous, inside the request's SERIALIZABLE transaction |
| On failure | 503, rolling back the whole request. No retries |

As a result, authenticated APIs cannot be called, responses cannot be used, and if COMMIT fails after sending, the external
side has received it while the DB is rolled back (non-atomicity). External integration can only be used for "fire a
notification" purposes.

## 2. List of decisions

| # | Issue | Decision |
|---|---|---|
| D1 | Destination | Declare named destinations in the sources (`@external` on a reserved-style `entity Stripe;`). The base URL and the authentication scheme are in the sources; the key is an environment variable of the core configuration. Handlers can build neither the URL nor headers |
| D2 | Call | Pass it through the authorization layer as a declared effect `@effect("call …")`. nyxis builds the body from the target row's columns, the proposed values in `context.values`, and the generated values |
| D3 | Where the response goes | Decode the response into the type declared in the sources and pass it to the handler as a value (the alternative of nyxis writing directly to columns was not adopted). To write to the DB, the handler calls a separate action, which goes through the normal decision |
| D4 | Timing | Determined by the sources (the handler does not choose). `sync` returns a response and runs synchronously inside the transaction; `async` has no response, is written to the outbox and COMMITted, and is sent later |
| D5 | Non-atomicity of sync | Accept it and document it. When calling an API with side effects via sync, use the request's unique ID `context.id` as the idempotency key (trusted assumption: Assumption 3) |
| D6 | Where the outbox lives | nyxis's reserved table `_nyxis_outbox`. It does not appear in the sources and is not visible to the application's policies |
| D7 | Sender | nyxis's own internal loop, not a scheduled job of a service principal. No re-decision at send time (permit happens once, at write time) |
| D8 | Final state of failures | Rows exceeding the maximum number of attempts remain as `failed`; nyxis does not delete them. For now there is no effect for the application to read them (operators look at them directly with SQL) |
| D9 | Type checking of responses | Lenient. Only missing declared keys and type mismatches are rejected; extra keys are dropped |
| D10 | Non-2xx for sync | Not a 503; the status code and the raw body are passed to the handler (`Outcome.calledError`). The handler can map business failures (402, 422, etc.) to 400, 409, etc. |
| D11 | Limits | The same level as the existing webhook, changeable via the core configuration. The total-transfer limit of sync can be overridden with a shorter one per effect |
| D12 | The existing `webhook` effect | Absorbed into `call` with `async` and removed (the only difference from the current one is that the destination is the value of a row's column, which is kept as `url: column` in §3.3). `mail` is kept because it is a different transport (SMTP) |

## 3. Grammar of the sources

### 3.1 Declaring a destination (entity side)

```
@external("base: https://api.stripe.com; auth: bearer NYXIS_EXT_STRIPE")
entity Stripe;
```

- Reserved-style, like `Service` / `Anonymous`. Not a table, and cannot have attributes, parents, or tags. It cannot be
  written as either the principal or the resource of an action's `appliesTo` (it is named only inside effects).
- `base`: a fixed base URL starting with `https://`. It may contain a path. A trailing `/` is normalized.
- `auth`: one of the following 3 kinds. Only the environment variable name appears in the sources; the value is passed via
  the core configuration. If it is not set, startup is refused.
  - `bearer <environment variable name>` — `Authorization: Bearer <value>`
  - `header <header name> <environment variable name>` — any single header (e.g. `header X-API-Key NYXIS_EXT_MAPS`)
  - `none`
- Any number of destinations can be declared in one set of sources.

### 3.2 Declaring an operation (action side)

```
@effect("call Stripe POST /v1/charges T(amount, currency) sync -> { id: String, status: String }")
action "chargeOrder" appliesTo {
  principal: [User],
  resource: [Order],
  context: { "values": { "amount": Long, "currency": String }, "id": String }
};
```

Grammar (one effect per action, as before):

```
call <destination> <method> <path> <T>(<column>, …) (sync [<seconds>s] -> <record type> | async)
```

- `<destination>`: the name of a reserved-style type with `@external`. Rejected if absent.
- `<method>`: `GET` / `POST` / `PUT` / `PATCH` / `DELETE`.
- `<path>`: a fixed string. Only `{key}` can be filled in, with the target row's primary key (handler and column values do
  not enter the path). `?` and `#` are rejected. APIs that need a query string cannot be substituted with a body, so they are
  out of scope for now.
- `<T>(<column>, …)`: the target row's columns to put in the body. `T` is the table in the action's `resource`. An empty `T()`
  is also allowed. `GET` / `DELETE` send no body, so no columns can be written.
- For an action that declares `context.values`, the proposed values are also merged into the body (rejected if one has the
  same name as a column). Policies can narrow with `context.values` (e.g. `context.values.currency == "jpy"`).
- The body is a JSON object. The value mapping is the same as `CallSend.jsonOf` (formerly `WebhookSend.jsonOf`) (entity
  references become the ID, datetimes epoch milliseconds, decimals strings, sets arrays, records objects). Generated values
  are included by mapping `context.id` into `values` (nyxis adds no keys to the body on its own).
- `sync [<seconds>s] -> <record type>`: the response type. A Cedar record type (`{ name: type, name?: type }`; nesting, `Set`,
  and extension types such as `datetime` are allowed). `<seconds>s` overrides the total-transfer limit (only with a value
  shorter than the core configuration's default).
- `async`: no response. Goes via the outbox.

### 3.3 When the destination is a row's column (successor of the current webhook)

```
@external("auth: none")
entity Hook;

@effect("call Hook POST url: endpoint T(title, body) async")
```

- A destination whose `@external` has no `base` uses `url: <column>`, a String column of the target row, as the destination.
  Only values starting with `https://` are allowed, and the policy narrows with `resource.endpoint like "https://hooks.example/*"`
  (same as now).
- Combining `base` and `url:` is rejected. A `url:` destination can also be written with `sync`, but that means waiting
  synchronously on an unspecified destination, so `async` is recommended (documented only, not enforced).

### 3.4 What is rejected at build time (added to `CedarSchema.elaborate`)

- `call` names a type without `@external`. The `base` of `@external` is not `https://`, or `auth` is malformed.
- Placeholders other than `{key}`, paths containing `?` / `#`.
- Body columns on `GET` / `DELETE`. Missing columns, duplicates, columns with the same name as one in `values`.
- A `sync` response type that cannot be built as a Cedar record type. `->` on `async`.
- Writing an `@external` type as the principal or resource of `appliesTo`, or giving it attributes or parents.

## 4. Execution flow

### 4.1 sync

Performed as one stage of `PostgresRun.runStaged`, at the same position as existing external effects.

1. Fetch the decision materials → check coverage → `Authz.step`. If not permitted, `denied` (mapped to 403). Nothing is sent.
2. If permitted, record `Authz.Payload.call`. Contents: destination name, method, resolved URL, body (a list of column names
   and values). The value of the authentication header is not included in the record (it is added from the core
   configuration at send time).
3. `Driver.external` sends it. Transport follows the same curl policy as the current webhook (`--disable`, HTTPS only, no
   redirect following, `--noproxy *`, `--globoff`).
4. Response:
   - Transport failure (connection, TLS, timeout, body limit exceeded): exception → the whole request is 503, the
     transaction is rolled back.
   - 2xx: decode the body as JSON and check it leniently against the declared type (D9). If it does not match, 502 and
     rollback. If it matches, continue the handler with `Outcome.called (value : Cedar.Spec.Value)`.
   - Non-2xx: continue the handler with `Outcome.calledError (status : Nat) (body : String)`. `body` is the raw string
     (with the same limit as the response body). The transaction continues.
5. Non-atomicity (D5): COMMIT can fail after sending. nyxis does not prevent this; it is documented as Assumption 3
   (idempotency keys).

### 4.2 async

1. Likewise, decide → if permitted, record `Payload.call`.
2. `Driver.external` does not send; it INSERTs one row into `_nyxis_outbox` (in the same transaction). The handler receives
   `Outcome.ok none`.
3. Finalized by COMMIT. If it fails, the outbox row does not remain either (atomicity).
4. nyxis's internal loop (separate from `Jobs`; `Outbox.loop`) takes `pending` rows and sends them.
   - Rows are taken one at a time with `FOR UPDATE SKIP LOCKED` (avoiding double sends across multiple instances). The
     loop's transaction is READ COMMITTED (not the request's SERIALIZABLE; for a queue that reads the same predicate and
     updates different rows, under SERIALIZABLE the COMMIT after sending is rolled back by a serialization failure and the
     same row is resent — measured in the integration test). A row whose state update or COMMIT after sending failed (the
     process crashed) remains `pending` and is resent (delivery is at least once).
   - 2xx: `sent`.
   - 5xx, transport failure: increment `attempts` and determine the next time with exponential backoff.
   - 4xx: immediately `failed` (retrying would not change it).
   - Maximum number of attempts exceeded: `failed`.
5. The response body is discarded (`async` has no response type).

### 4.3 Shape of `_nyxis_outbox`

| Column | Type | Contents |
|---|---|---|
| `_nyxis_id` | text PK | The request's unique ID + the stage number (one request can have multiple async calls) |
| `principal` | text | The principal of the record (for auditing; not used for send decisions) |
| `action` | text | The decided action |
| `target` | text | The target `table/<primary key>` |
| `destination` | text | Destination name |
| `method` / `url` | text | Resolved |
| `body` | jsonb | Body |
| `state` | text | `pending` / `sent` / `failed` |
| `attempts` | int | Number of attempts |
| `next_at` | timestamptz | Time of the next attempt |
| `last_status` / `last_error` | int / text | The last response. `last_error` contains no diagnostic strings (only a category) |
| `created_at` / `sent_at` | timestamptz | |

- Same DB and same role as the sources' tables. `PostgresInit` creates it together with the sources' tables (for any
  sources; it stays empty if there is no `async` declaration; a table named `_nyxis_outbox` cannot be written in the
  sources). A partial index on only the `pending` rows, `_nyxis_outbox_pending_idx (next_at) WHERE state = 'pending'`, is
  added (so that the cost of one loop iteration does not depend on the number of sent or failed rows; columns, states, and
  transitions are unchanged).
- `_nyxis_id` is `<the request's unique ID>-<which async call of that request it is>` (the number of rows of the same
  request written earlier in the same transaction). The categories of `last_error` are `status` (a non-2xx response) /
  `transport` (connection, TLS, deadline, body limit) / `config` (the destination is not in the configuration, or the URL
  is not HTTPS; not retried) / `attempts` (maximum number of attempts exceeded).
- Not reachable from the application's handlers or policies (not in `Authz.Schema.tables`). No effect for reading it is
  added for now (D8).

## 5. Core configuration

| Environment variable | Contents | Default |
|---|---|---|
| `NYXIS_EXT_<name>` (the name the sources' `auth` refers to) | Key per destination | Required (startup is refused if unset) |
| `NYXIS_CALL_CONNECT_TIMEOUT` | Connection (seconds) | 3 |
| `NYXIS_CALL_MAX_TIME` | Total transfer (seconds). A sync `<seconds>s` can only be shorter than this | 10 |
| `NYXIS_CALL_MAX_RESPONSE_BYTES` | Response body | 65536 |
| `NYXIS_OUTBOX_INTERVAL_SECONDS` | Interval of the internal loop | 5 |
| `NYXIS_OUTBOX_MAX_ATTEMPTS` | Maximum number of attempts | 8 |
| `NYXIS_OUTBOX_BACKOFF_BASE_SECONDS` | Backoff base (`base × 2^attempts`) | 10 |

## 6. Additions to the theorem

The statement of `Nyxis.Runtime.authorization_safety` is unchanged; items of the same form as (6) and (7) are added.

- **(8)** Every recorded call (`Payload.call`; both sync and async) is permitted, for that request's principal and generated
  values, with the same decision materials as a read of the target row; its destination, method, and path come from the
  sources' declaration, and its body is what nyxis determined from the target row's declared columns and the proposed
  values in `context.values`. Each row of the outbox is exactly this record.
- **(9)** A response value passed to a handler (`Outcome.called` / `calledError`) is an arbitrary value coming from that
  call's result list (`Runtime.Externals`, widened from `Option String` to the response sum type `Authz.ExternalResult`),
  and does not change the decision (the operations issued or the records) (an extension of the current
  `Authz.step_external_indep`). The only way a response value reaches the DB is through `values` that the handler proposes
  in a separate action, which go through the decision in (1).

Changes to the pure model:
`call (destination : String) (method : CallMethod) (target : CallTarget) (columns : List Column) (proposes : Bool) (mode : CallMode)`
in `Db.EffectKind`, `call` in `Authz.Payload`, `called` / `calledError` in `Outcome`, and the element type of `Runtime.Externals`. The proven
scope of the connection code (`StagedRun.external`: `Driver.external` is called only for recorded contents) is stated in the
same form for the async INSERT and `Outbox.loop` (the loop sends only the contents of outbox rows). The outside-world
behavior of `Outbox.loop` (interval, retries) is, like `Jobs.loop`, unproven and remains under Assumption 1 (connection code).

## 7. Open questions

- **The receiving side** (callbacks / inbound webhooks from external services). A candidate is to declare the principal of
  requests without a JWT in the sources as an "external principal" with signature verification. To be addressed after the
  sending side is settled.
- APIs that need a query string (`GET /v1/search?q=…`). They cannot be substituted with a body, so a safe embedding such as
  `{values.q}` will be considered later.
- An effect for handlers to read the outbox's state (deferred under D8).
- Types of external values that cannot be expressed as Cedar record types (arrays of arrays, distinguishing `null` from
  absence).

import Nyxis.Internal.CallSend

/-!
# Test.CallSend — the pure parts of the connection layer for external API calls

Checks with `#guard` the lenient decoding of responses (`CallSend.decode`: only missing declared keys and type
mismatches are rejected, and extra keys are dropped), the body JSON, the curl configuration (the authentication header
and the body are placed only inside the configuration), and the splitting of curl's output. Actual sending (HTTPS to a
mock API) is done in the integration tests (`Test.ExternalCalls` and `scripts/check-external-calls.py`).
-/

namespace Test.CallSend

open Cedar.Spec
open Cedar.Data
open Nyxis.Db
open Nyxis.Internal.CallSend

def strV (s : String) : Value := .prim (.string s)
def intV (n : Int) : Value := .prim (.int (Int64.ofInt n))

def chargeTy : Cedar.Validation.CedarType :=
  .record (Map.make [("id", .required .string), ("status", .required .string),
    ("meta", .optional (.record (Map.make [("n", .required .int)]))),
    ("tags", .optional (.set .string)), ("when", .optional (.ext .datetime)), ("owner", .optional (.entity ⟨"User", []⟩))])

def parse (s : String) : Lean.Json := (Lean.Json.parse s).toOption.getD .null

-- Only the declared keys remain; extra keys are dropped
#guard decode chargeTy (parse "{\"id\":\"ch_1\",\"status\":\"ok\",\"extra\":[1,2]}")
  == some (.record (Map.make [("id", strV "ch_1"), ("status", strV "ok")]))
-- Optional keys are decoded if present and absent otherwise. Nesting, sets, datetimes, entity references
#guard decode chargeTy (parse "{\"id\":\"c\",\"status\":\"s\",\"meta\":{\"n\":7,\"x\":1},\"tags\":[\"a\",\"b\",\"a\"],\"when\":1700000000000,\"owner\":\"alice\"}")
  == some (.record (Map.make [("id", strV "c"), ("status", strV "s"), ("meta", .record (Map.make [("n", intV 7)])),
    ("tags", .set (Set.make [strV "a", strV "b"])), ("when", .ext (.datetime ⟨1700000000000⟩)),
    ("owner", .prim (.entityUID ⟨⟨"User", []⟩, "alice"⟩))]))
-- Missing non-optional keys and type mismatches (top level, nested, set elements) are rejected
#guard decode chargeTy (parse "{\"id\":\"ch_1\"}") == none
#guard decode chargeTy (parse "{\"id\":1,\"status\":\"ok\"}") == none
#guard decode chargeTy (parse "{\"id\":\"c\",\"status\":\"s\",\"meta\":{\"n\":\"seven\"}}") == none
#guard decode chargeTy (parse "{\"id\":\"c\",\"status\":\"s\",\"meta\":{}}") == none
#guard decode chargeTy (parse "{\"id\":\"c\",\"status\":\"s\",\"tags\":[\"a\",1]}") == none
-- Non-object responses and null are rejected
#guard decode chargeTy (parse "[1]") == none
#guard decode chargeTy (parse "null") == none
#guard decode chargeTy (parse "{\"id\":null,\"status\":\"s\"}") == none
-- Integers: fractions are rejected, values outside the Int64 range are rejected. Numbers denoting integers such as 1e2
-- are accepted
#guard decode .int (parse "12") == some (intV 12)
#guard decode .int (parse "1.5") == none
#guard decode .int (parse "1e2") == some (intV 100)
#guard decode .int (parse "9223372036854775808") == none
#guard decode .int (parse "-9223372036854775808") == some (.prim (.int (Int64.ofInt (-9223372036854775808))))
-- Booleans, strings, decimals
#guard decode (.bool .anyBool) (parse "true") == some (.prim (.bool true))
#guard decode .string (parse "\"x\"") == some (strV "x")
#guard decode (.ext .decimal) (parse "\"1.5\"") == some (.ext (.decimal (Int64.ofInt 15000)))
#guard decode (.ext .decimal) (parse "1.5") == none

-- The body JSON: column names and values (entity references are the ID, datetimes epoch milliseconds; key order does
-- not matter as long as the JSON is the same)
#guard (Lean.Json.parse (body [("subject", strV "s"), ("n", intV 7), ("doc", .prim (.entityUID ⟨⟨"Doc", []⟩, "d1"⟩)),
  ("at", .ext (.datetime ⟨1700000000000⟩))])).toOption == some (parse "{\"subject\":\"s\",\"n\":7,\"doc\":\"d1\",\"at\":1700000000000}")

-- The curl configuration: the URL, method, body (with Content-Type), and authentication header are only inside the
-- configuration. With GET there is neither a body nor a Content-Type
#guard configText "https://api.example/v1/charges/n1" .post (some [("n", intV 7)]) (some "Authorization: Bearer secret")
  == "url = \"https://api.example/v1/charges/n1\"\nrequest = \"POST\"\nheader = \"Content-Type: application/json\"\ndata = \"{\\\"n\\\":7}\"\nheader = \"Authorization: Bearer secret\"\n"
#guard configText "https://api.example/v1/charges/n1" .get none none
  == "url = \"https://api.example/v1/charges/n1\"\nrequest = \"GET\"\n"
-- The authentication header, URL, and body do not appear in the arguments (only the fixed transport policy)
#guard (arguments 3 10 65536).all fun a => !(a.splitOn "Authorization").length > 1 && !(a.splitOn "https://").length > 1
#guard (arguments 3 7 1024).contains "7" && (arguments 3 7 1024).contains "1024" && (arguments 3 7 1024).contains "=https"

-- Splitting the output: body + newline + status code
#guard splitOutput "{\"id\":\"c\"}\n200" == some (200, "{\"id\":\"c\"}")
#guard splitOutput "line1\nline2\n404" == some (404, "line1\nline2")
#guard splitOutput "\n204" == some (204, "")
#guard splitOutput "no code" == none

-- The header line per authentication scheme (loading the configuration requires environment variables, so only the
-- shape of the line)
#guard (CallMethod.get.hasBody, CallMethod.delete.hasBody, CallMethod.post.hasBody, CallMethod.put.hasBody,
  CallMethod.patch.hasBody) == (false, false, true, true, true)
#guard [CallMethod.get, .post, .put, .patch, .delete].map CallMethod.name == ["GET", "POST", "PUT", "PATCH", "DELETE"]

end Test.CallSend

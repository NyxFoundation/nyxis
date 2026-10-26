import Nyxis.Internal.JwksFetch

open Nyxis.Internal.JwksFetch

#guard urlOfIssuer "https://example.supabase.co/auth/v1" ==
  some "https://example.supabase.co/auth/v1/.well-known/jwks.json"
#guard urlOfIssuer "https://localhost:443/auth/v1" ==
  some "https://localhost:443/auth/v1/.well-known/jwks.json"
#guard (["http://example.com/auth/v1", "https://user@example.com/auth/v1",
  "https://example.com/auth/v1/", "https://example.com/auth/v1?x=1",
  "https://example.com/auth/v1#x", "https://example.com:0/auth/v1",
  "https://example.com:65536/auth/v1", "https://example.com:x/auth/v1",
  "https://-host/auth/v1", "https://host../auth/v1", "https://[::1]/auth/v1",
  "https://host%2ecom/auth/v1", "https://ho st/auth/v1", "https://host\n/auth/v1",
  "https://host\\other/auth/v1", "https://host/auth/v1\x00",
  "https://{host,other}/auth/v1", "--insecure"].all (urlOfIssuer · == none))
#guard supportedVersion "curl 8.4.0 (test)"
#guard supportedVersion "curl 8.7.1 (test)"
#guard supportedVersion "curl 9.0.0 (test)"
#guard !supportedVersion "curl 8.3.9 (test)"
#guard !supportedVersion "curl 7.99.0 (test)"
#guard !supportedVersion "curl nonsense"
#guard documentOfOutput 0 "{\"keys\":[]}\n200" == some "{\"keys\":[]}"
#guard documentOfOutput 0 "a\n200\nb\n200" == some "a\n200\nb"
#guard documentOfOutput 0 "\n200" == none
#guard documentOfOutput 0 "{}\n201" == none
#guard documentOfOutput 0 "{}\n302" == none
#guard documentOfOutput 28 "{}\n200" == none
#guard documentOfOutput 0 (String.ofList (List.replicate 65536 'x') ++ "\n200") |>.isSome
#guard documentOfOutput 0 (String.ofList (List.replicate 65537 'x') ++ "\n200") == none
#guard documentOfOutput 0 (String.ofList (List.replicate 32769 'é') ++ "\n200") == none

/-- Transport probe only; not an application or HTTP API. CA and executable
configuration are inherited from the test process's deployment environment. -/
def main (args : List String) : IO Unit := do
  let [issuer] := args | throw (IO.userError "expected issuer")
  let result ← fetch issuer
  IO.println (if result.isSome then "accepted" else "rejected")

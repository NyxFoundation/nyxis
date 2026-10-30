#!/usr/bin/env python3
"""Compile isolated Cedar-source declarations, without touching application sources.

Run after lake build. Fixtures live outside the repository, so relative path resolution
cannot accidentally rely on the working directory or the official application's files.
"""
from pathlib import Path
import subprocess
import tempfile

if not __debug__:
    raise SystemExit('assertions disabled')
ROOT = Path(__file__).resolve().parent.parent
SCHEMA = '''entity Record = { "visible": Bool };
entity Anonymous;
@effect("read Record")
action "view" appliesTo { principal: [Anonymous], resource: [Record] };
'''
POLICY = '''permit (principal, action == Action::"view", resource is Record)
when { resource.visible };
'''
HEADER = '''import Nyxis.AppCheck
namespace DeclarationCheck
nyxis_approved sources from "schema.cedarschema" and "policies.cedar"
'''
VALID = HEADER + '''
#guard sources.schema.tables.length == 1
#guard sources.policies.length == 1
example (router : Nyxis.Http.Router) :
    (sources.app router).schema = sources.schema := rfl
example (router : Nyxis.Http.Router) :
    (sources.app router).policies = sources.policies := rfl
end DeclarationCheck
nyxis_check_app
'''


def main():
    with tempfile.TemporaryDirectory(prefix="nyxis-approved-declaration-") as directory:
        fixture = Path(directory) / "nested"
        fixture.mkdir()
        schema = fixture / "schema.cedarschema"
        policy = fixture / "policies.cedar"
        source = fixture / "Check.lean"

        def check(label, text=VALID, schema_text=SCHEMA, policy_text=POLICY, error=None):
            schema.write_text(schema_text)
            policy.write_text(policy_text)
            source.write_text(text)
            result = subprocess.run(
                ["lake", "env", "lean", str(source)], cwd=ROOT,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                timeout=120, check=False,
            )
            if error is None:
                assert result.returncode == 0, f"{label}: {result.stdout}"
            else:
                assert result.returncode != 0 and error in result.stdout, (
                    f"{label}: exit {result.returncode}: {result.stdout}"
                )
            print(f"ok: {label} (lean exit {result.returncode})")

        check("relative sources outside repository; application audit; fixed App fields")
        check("missing schema", text=VALID.replace('"schema.cedarschema"', '"absent-schema"'),
              error="スキーマ")
        check("missing policies", text=VALID.replace('"policies.cedar"', '"absent-policies"'),
              error="ポリシー")
        check("missing effect", schema_text=SCHEMA.replace('@effect("read Record")', ''),
              error="効果の宣言(@effect)が無い")
        check("unknown table", schema_text=SCHEMA.replace('read Record', 'read Missing'),
              error="Missing")
        check("unknown update column", schema_text=SCHEMA.replace('read Record', 'update Record(missing)'),
              error="missing")
        check("malformed policy", policy_text="permit (", error="nyxis:")
        check("declaration cannot erase policies", text=HEADER + '''
example (router : Nyxis.Http.Router) : (sources.app router).policies = [] := rfl
end DeclarationCheck
''', error="Type mismatch")
        check("declaration cannot erase schema", text=HEADER + '''
example (router : Nyxis.Http.Router) : (sources.app router).schema.tables = [] := rfl
end DeclarationCheck
''', error="Type mismatch")
        check("valid declaration after rejected variants")
        startup = HEADER.replace("import Nyxis.AppCheck", """import Nyxis.Internal.ApprovedServer
import Nyxis.Internal.PostgresShapeBuild""") + """
nyxis_postgres_shape shape from "schema.cedarschema"
def deployment : Nyxis.Internal.ApprovedServer.Deployment where
  sources := sources
  shape := shape
  shape_valid := by rfl
  userType := ⟨"Actor", []⟩
  user_not_anonymous := by decide
  user_not_service := by decide
example (router : Nyxis.Http.Router) :
    Nyxis.Internal.ApprovedServer.serve deployment 8080 "unused" "unused" router {} = (do
      Nyxis.Internal.JwksFetch.requireCurl
      Nyxis.Internal.Jobs.start "unused" (sources.app router) shape {} none
      Nyxis.Internal.Outbox.start "unused" sources.schema none {}
      Nyxis.Internal.PostgresHttp.serveVerifiedApp 8080 "unused" (sources.app router)
        shape ⟨"Actor", []⟩ (Nyxis.Internal.JwksFetch.verify "unused") {}) := rfl
end DeclarationCheck
"""
        check("generic startup uses external sources, shape and Actor type", text=startup)
        check("startup rejects missing shape proof", text=startup.replace(
            '  shape_valid := by rfl\n', ''), error="shape_valid")
        check("startup rejects unrelated shape at compile time", text=startup.replace(
            '  shape := shape', '  shape := []'), error="rfl")
        replacement = startup.replace('end DeclarationCheck', """
def replacement : Nyxis.Runtime.App :=
  { schema := sources.schema, policies := [], router := fun _ _ => none }
end DeclarationCheck
""")
        check("replacement App fixture is well typed", text=replacement)
        check("startup cannot accept replacement App", text=replacement.replace(
            'end DeclarationCheck', '''
def rejected := Nyxis.Internal.ApprovedServer.serve deployment 8080 "unused" "unused" replacement
end DeclarationCheck
'''), error="Application type mismatch")
        check("bridge import remains rejected by application audit", text="""import Nyxis.AppCheck
import Nyxis.Internal.ApprovedServer
nyxis_check_app
""", error="nyxis app audit")
        check("valid generic startup after rejected variants", text=startup)

    print("approved declaration: 17 compilation checks passed; temporary fixtures removed")


if __name__ == "__main__":
    main()

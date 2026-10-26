#!/usr/bin/env python3
"""OpenSSL-generated, throwaway fixture keys; never application credentials."""
import base64
from pathlib import Path
import re
import subprocess
import sys
import json

if not __debug__:
    raise SystemExit('assertions disabled')
work = Path(sys.argv[1])
# Generate throwaway fixture material with OpenSSL, never application or Supabase keys.
# Read OpenSSL's public coordinate output solely to write the JWKS test fixture.
subprocess.run(["openssl", "genpkey", "-algorithm", "EC", "-pkeyopt",
                "ec_paramgen_curve:P-256", "-out", str(work / "test-key.pem")], check=True)
public = subprocess.check_output(["openssl", "pkey", "-in", str(work / "test-key.pem"),
                                  "-text_pub", "-noout"], text=True)
point = public.split("pub:", 1)[1].split("ASN1 OID:", 1)[0]
point = bytes.fromhex("".join(re.findall(r"[0-9a-f]{2}(?=:|\s|$)", point)))
assert len(point) == 65 and point[0] == 4, "unexpected OpenSSL P-256 public point"
def b64(data):
    return base64.urlsafe_b64encode(data).decode().rstrip("=")
(work / "test-jwks.json").write_text(json.dumps({"keys": [{
    "kty": "EC", "crv": "P-256", "alg": "ES256", "kid": "test",
    "x": b64(point[1:33]), "y": b64(point[33:]),
}]}))

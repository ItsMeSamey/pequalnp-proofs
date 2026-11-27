"""Replay or generate a certificate from explicit care and source-model files."""

import argparse
import json
from pathlib import Path
from fork_certificate import make_certificate, verify_case, verify_optional_family


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("action", choices=["verify", "generate", "verify-family"])
    p.add_argument("--care", type=Path, required=True)
    p.add_argument("--rows-key", help="Optional field containing rows in a manifest.")
    p.add_argument("--feature-count", type=int, required=True)
    p.add_argument("--model", type=Path, required=True)
    p.add_argument("--certificate", type=Path, required=True)
    p.add_argument("--plan", type=Path, help="For generation, a JSON budget and cases.")
    a = p.parse_args()
    data = json.loads(a.care.read_bytes())
    rows = data[a.rows_key] if a.rows_key is not None else data
    model = json.loads(a.model.read_bytes())
    if a.action == "generate":
        if a.plan is None or a.certificate.exists():
            p.error("generate requires --plan and a fresh certificate destination")
        plan = json.loads(a.plan.read_bytes())
        cert = make_certificate(
            rows, a.feature_count, model, plan["budget"], plan["cases"]
        )
    else:
        if a.plan is not None:
            p.error("--plan applies only to generate")
        cert = json.loads(a.certificate.read_bytes())
    checker = verify_optional_family if a.action == "verify-family" else verify_case
    result = checker(rows, a.feature_count, model, cert)
    if a.action == "generate":
        with a.certificate.open("x") as f:
            json.dump(cert, f, separators=(",", ":"))
            f.write("\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()

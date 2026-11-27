"""Verify the local source closure and print the terminal audit records."""
import hashlib
import json
from pathlib import Path
from zipfile import ZipFile

here = Path(__file__).resolve().parent
manifest_bytes = (here / "h1joined-manifest.json").read_bytes()
manifest = json.loads(manifest_bytes)
receipt = here / "h1joined-receipts-1459d7750cafcd4e.zip"
assert hashlib.sha256(receipt.read_bytes()).hexdigest() == "feadcaf8ba3ca4a0436fa5d2748391685a482a4b180b72030373740ec8c0eb5d"
with ZipFile(here / "project-sources.zip") as sources, ZipFile(receipt) as audit:
    assert len(manifest["modules"]) == len(sources.namelist()) == 1505
    assert len(manifest["external_inputs"]) == 14
    assert audit.read("h1joined-manifest.json") == manifest_bytes
    for name, record in manifest["modules"].items():
        data = sources.read(name.replace(".", "/") + ".lean")
        assert hashlib.sha256(data).hexdigest() == record["source_sha256"]
        if name in ("H1CoverAllDirect9822", "H1OriginalJoinedFloor9822", "H1ReducedSector9822"):
            assert data == audit.read(f"{name}/{name}.lean")
            print(audit.read(f"{name}/{name}.log").decode().strip())
print("Verified 1,505 project sources, manifest for 14 external inputs, and three terminal receipts.")

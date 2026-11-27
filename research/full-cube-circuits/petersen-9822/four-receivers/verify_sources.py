"""Verify the local source closure and print the terminal audit records."""
import hashlib
import json
from pathlib import Path
from zipfile import ZipFile

here = Path(__file__).resolve().parent
manifest_bytes = (here / "d3orig-manifest.json").read_bytes()
manifest = json.loads(manifest_bytes)
receipt = here / "d3orig-receipts-edfd9fa12a79c4a4.zip"
assert hashlib.sha256(receipt.read_bytes()).hexdigest() == "bb6c8c8b0b31febd3a0dad3c375b6973fb916b6d62825f73308c17fcf6a4b51a"
with ZipFile(here / "project-sources.zip") as sources, ZipFile(receipt) as audit:
    assert len(manifest["modules"]) == len(sources.namelist()) == 731
    assert len(manifest["external_inputs"]) == 14
    assert audit.read("d3orig-manifest.json") == manifest_bytes
    for name, record in manifest["modules"].items():
        data = sources.read(name.replace(".", "/") + ".lean")
        assert hashlib.sha256(data).hexdigest() == record["source_sha256"]
        if name in ("SixD3ClosedBoth9822", "SixD3OriginalFour9822", "SixD3OriginalProjection9822"):
            assert data == audit.read(f"{name}/{name}.lean")
            print(audit.read(f"{name}/{name}.log").decode().strip())
print("Verified 731 project sources, manifest for 14 external inputs, and three terminal receipts.")

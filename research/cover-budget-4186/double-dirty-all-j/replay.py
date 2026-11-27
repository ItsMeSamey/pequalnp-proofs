"""Verify frozen files and the outputs of the finite profile checks."""
from pathlib import Path
import hashlib
import subprocess
import sys

root = Path(__file__).resolve().parent
for manifest in [root / 'SHA256SUMS', root / 'freeze-4186-private-mixer' / 'SHA256SUMS']:
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ',1)
        if hashlib.sha256((manifest.parent / name).read_bytes()).hexdigest() != digest:
            raise SystemExit(f'checksum mismatch: {name}')
for script, receipt in [
    ('freeze-4186-private-mixer/profile_check.py','private.txt'),
    ('bounds_4186_shared_defects.py','single-large.txt'),
    ('4186-small-triangle.py','small-triangle.txt'),
    ('quantifiers_4186_triangle.py','rich-triangle.txt'),
]:
    observed = subprocess.check_output([sys.executable,'-B',str(root / script)],cwd=root)
    if observed != (root / 'receipts' / receipt).read_bytes():
        raise SystemExit(f'output changed: {script}')
    print(f'OK {script}')

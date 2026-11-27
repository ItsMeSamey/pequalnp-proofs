"""Verify source hashes and reproduce every expected CLI result."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
root=Path(__file__).resolve().parent
for line in (root/'SHA256SUMS').read_text().splitlines():
    digest,name=line.split('  ',1)
    if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
        sys.exit('hash mismatch: '+name)
for case in json.loads((root/'manifest.json').read_text()):
    output=subprocess.check_output([sys.executable,'-B',str(root/'constructive-abi-audit/convert.py'),str(root/case['input'])])
    if output!=(root/case['output']).read_bytes():
        sys.exit('output mismatch: '+case['name'])
    print(case['name'],case['branch'],case['sizes'])

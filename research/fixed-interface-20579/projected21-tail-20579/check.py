"""Check the local manifest, projection, and projected-tail size exclusion."""
from pathlib import Path
import hashlib
import runpy

here = Path(__file__).resolve().parent
for line in (here/'SHA256SUMS').read_text().splitlines():
    digest, name = line.split('  ',1)
    if hashlib.sha256((here/name).read_bytes()).hexdigest() != digest:
        raise ValueError('digest mismatch',name)
for script in ['verify_projection.py','verify_projected_two_not28.py','verify_precone_regions.py']:
    runpy.run_path(str(here/script),run_name='__main__')
print('Verified 28-gate lower bound for this 21-feature scalar tail.')

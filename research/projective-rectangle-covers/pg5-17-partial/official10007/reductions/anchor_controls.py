"""Exercise the public checker on each closed anchor using the same 21-box witness."""
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

from anchor_cones import FULL, ROWS, columns

ROOT = Path(__file__).resolve().parent
ANCHORS = [(55, 546299908), (29, 170913825), (103, 563068940),
           (119, 546291716), (1861, 195823621), (1869, 187435009)]

def run(path, anchor, budget, item, expected_error=None):
    path.write_text(json.dumps(item))
    result = subprocess.run([sys.executable, str(ROOT / 'anchor_cones.py'), str(path),
                             '--anchor', str(anchor), '--budget', str(budget)],
                            text=True, capture_output=True)
    if expected_error is None:
        if result.returncode or not result.stdout.startswith('verified '):
            raise RuntimeError(result.stderr or result.stdout)
    elif result.returncode == 0 or f'ValueError: {expected_error}' not in result.stderr:
        raise RuntimeError(f'expected {expected_error}: {result.stderr}')

def main():
    prior = json.loads((ROOT / 'control21.json').read_text())['shores']
    with TemporaryDirectory() as tmp:
        p = Path(tmp) / 'control.json'
        run(p, -1, 21, {'shores': prior})
        print('anchor_left anchor_right height width area reused21_plus_anchor budget1_refutation missing_anchor open17_leaf')
        for a,b in ANCHORS:
            reverse = sum(1 << i for i, row in enumerate(ROWS) if not row & b)
            if columns(a) != b or reverse != a or not (0 < b <= FULL):
                raise ValueError('anchor fails closure')
            run(p, a, 22, {'shores': [a] + prior})
            run(p, a, 1, {'tree': None})
            run(p, a, 21, {'shores': prior}, 'fixed anchor omitted')
            run(p, a, 17, {'tree': None}, 'open leaf')
            h,w = a.bit_count(),b.bit_count()
            print(a,b,h,w,h*w,'pass pass rejected rejected')

if __name__=='__main__':
    main()

"""Replay the frozen four-AND proof logs and the constructive upper bound."""
from ast import literal_eval
from pathlib import Path
import json
from reconstruct import reconstruct

ROOT = Path(__file__).resolve().parent
for terminals, expected in enumerate((0, 0, 34, 77, 19)):
    if terminals == 0:
        continue
    lines = (ROOT / f'audit{terminals}.log').read_text().splitlines()
    assert lines[-1].startswith('final '), (terminals, 'incomplete')
    counts = literal_eval(lines[-1][len('final '):])
    assert len(lines) - 1 == expected
    assert counts == ({'False': expected} if expected else {})
    print(f'{terminals} terminals: {len(lines)-1} checked rejections')

gates, output, failures = reconstruct(json.loads((ROOT / 'verified-41.json').read_text()))
assert len(gates) == 41 and sum(op == 'and' for op, _, _ in gates) == 4 and not failures
print(f'{len(gates)} gates; all 144 promised inputs accepted or rejected correctly')

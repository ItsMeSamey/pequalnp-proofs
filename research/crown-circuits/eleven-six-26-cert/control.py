"""Exhaustively verify the constructive eleven-input control."""
from pathlib import Path
import json

record = json.loads((Path(__file__).parent / 'control27.json').read_text())
assert record['n'] == 11
assert len(record['gates']) == 27
assert sum(op == 'and' for op, _, _ in record['gates']) == 4
for bits in range(1 << 11):
    values = [bool(bits >> i & 1) for i in range(11)]
    for op, left, right in record['gates']:
        assert op in ('and', 'or') and 0 <= left < len(values) and 0 <= right < len(values)
        values.append((values[left] and values[right]) if op == 'and' else
                      (values[left] or values[right]))
    assert values[record['output']] == (bits.bit_count() >= 2)
print('27 gates, including four ANDs; all 2048 Boolean assignments verified')

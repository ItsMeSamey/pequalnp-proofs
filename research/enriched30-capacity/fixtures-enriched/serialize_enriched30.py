"""Serialize the pinned physical circuit and graph witnesses for Lean."""
import hashlib
import json
import re
from pathlib import Path

root = Path(__file__).resolve().parent
meta = json.loads((root / 'support.json').read_text())
raw = (root / meta['source']).read_bytes()
assert hashlib.sha256(raw).hexdigest() == '77e03122cec007ad85fdb752649fa2f19b4f65cf5d06317a66e411e68009a062'
net = json.loads(raw)['net']
bank = meta['bank']
statement = (root/'issued-statement.txt').read_text()
rows = [int(w, 16) for w in re.findall(r'0x[0-9a-fA-F]+', statement)]
assert len(rows) == 32 and len(bank) == len(set(bank)) == 30

def evaluate(cell):
    r, c = divmod(cell, 32)
    wires = [j in (r, 32+c) for j in range(64)]
    for g in net['gates']:
        op = g['op']
        assert op in ('and', 'or', 'not') and len(g['inputs']) == (1 if op=='not' else 2)
        args = [wires[i] for i in g['inputs']]
        wires.append(all(args) if op == 'and' else any(args) if op == 'or' else not args[0])
    return wires, (rows[r] >> c) & 1

cells = [evaluate(i) for i in range(1024)]
assert len(net['gates']) == 170 and sum(w[net['output']] != y for w,y in cells) == 14

def oriented(wire, pair):
    a,b = pair
    va,ya = cells[a]
    vb,yb = cells[b]
    assert ya != yb and [j for j in bank if va[j] != vb[j]] == [wire]
    return (b,a) if va[wire] else (a,b)

essential = [(int(k), *oriented(int(k), pair)) for k,pair in meta['mandatory_witness_cells'].items()]
assert {k for k,*_ in essential} == set(bank)-{90,137} and len(essential) == 28
pivots = json.loads((root/'chains.json').read_text())['(90, 137)']['target']['binate']
binate = []
for key, pair in pivots.items():
    wire = int(key)
    a,b = oriented(wire,pair['rise'])
    c,d = oriented(wire,pair['fall'])
    assert [cells[i][1] for i in (a,b,c,d)] == [0,1,1,0]
    binate.append((wire,a,b,c,d))
assert len(binate) == 11

gate_list = ',\n    '.join('⟨.'+g['op']+', '+str(g['inputs'])+'⟩' for g in net['gates'])
def tuples(lst):
    return '[\n    ' + ',\n    '.join(map(str, sorted(lst))) + ']'

out = f"""import PEqualNP.Defs.CircuitLowerBounds

namespace Enriched30Data

def circuit : PEqualNP.CircuitLowerBounds.Circuit where
  gates := [
    {gate_list}]
  output := {net['output']}

def bank : List Nat := {bank}

def rows : List Nat := {rows}

def target (cell : Fin 1024) : Bool :=
  (rows.getD (cell.val / 32) 0).testBit (cell.val % 32)

def essential : List (Nat × Nat × Nat) := {tuples(essential)}

def binate : List (Nat × Nat × Nat × Nat × Nat) := {tuples(binate)}

end Enriched30Data
"""
(root/'Enriched30Data.lean').write_text(out)

"""Check the witness on all inputs and the small graph arithmetic in the eight-AND proof."""
import json
from pathlib import Path
from math import comb
r=json.loads(Path(__file__).with_name('size32.json').read_text())
assert r['inputs']==13 and len(r['gates'])==32
for mask in range(8192):
    wires=[bool(mask>>i&1) for i in range(13)]
    for op,a,b in r['gates']:
        assert 0<=a<len(wires) and 0<=b<len(wires) and op in ('AND','OR')
        wires.append((wires[a] and wires[b]) if op=='AND' else (wires[a] or wires[b]))
    assert wires[r['output']]==(mask.bit_count()>=2)
print('32-gate upper witness accepted exactly the threshold-two inputs, 8192/8192.')
def partitions(n,minpart=1):
    if n==0:yield ();return
    for k in range(minpart,n+1):
        for t in partitions(n-k,k):yield (k,)+t
for p in range(5,9):
    # A quartet forces at least 3 components. Two quartets have at least 3p+2 incidences.
    for sizes in partitions(p):
        if len(sizes)<3 or 3*p+2>26:continue
        edge_need=3*p+2-13
        edge_cap=sum(comb(z,2) for z in sizes)
        if edge_cap<edge_need:continue
        # Isolated groups consume >=3 different labels each. Any graph with
        # only one nontrivial component uses >=edge_need distinct internal labels there.
        isolated=sizes.count(1)
        assert len(sizes)-isolated==1 and 3*isolated+edge_need>13,(p,sizes)
print('No pure incidence graph has two quartets under the stated precedents.')

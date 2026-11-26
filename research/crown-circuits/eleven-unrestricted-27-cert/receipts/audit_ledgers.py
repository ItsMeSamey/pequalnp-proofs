"""Audit the raw, chronology-indexed eleven-input six-switch rows and forest reindexing."""
from pathlib import Path
import argparse
import json
from collections import Counter
def numbers(p):
    return [tuple(map(int, row.split())) for row in p.read_text().splitlines() if row.strip()]
def branches(us):
    return [u & side for u, half in zip(us, halves) for side in (half, F ^ half)]
def observable(us):
    taps = branches(us)
    return {tuple(i for i,t in enumerate(taps) if t>>x&1):x for x in range(64)}
def forest(us):
    outputs = branches(us)
    children = [[[], []] for _ in us]
    roots = []
    for j,u in enumerate(us):
        if u==F:
            roots.append(j)
        else:
            parents = [i for i,v in enumerate(outputs[:2*j]) if u==v]
            assert len(parents)==1,(us,j,parents)
            p=parents[0];children[p//2][p%2].append(j)
    def rooted(j):
        return tuple(sorted(tuple(sorted(rooted(i) for i in side)) for side in children[j]))
    return tuple(sorted(rooted(j) for j in roots))
F=(1<<64)-1
halves=[sum(1<<x for x in range(64) if x>>j&1) for j in range(6)]
p=argparse.ArgumentParser()
p.add_argument('source',type=Path);p.add_argument('universe',type=Path);p.add_argument('forests',type=Path)
p.add_argument('--complete',action='store_true');a=p.parse_args()
U=numbers(a.universe);shapes=json.loads(a.forests.read_text())
hard={q:{} for q in (4,5)}
for i,us in enumerate(U):
    q=5-len(set(us)-set(branches(us))-{F})
    if q not in hard:continue
    atoms=observable(us);L=len(atoms)
    if L<11 or any(sum(not (u>>x&1) for x in atoms.values())<=2 for u in set(us)-{F}):continue
    hard[q][i]=(us,L)
for q in (4,5):
    expected=hard[q];rows=numbers(a.source/f'hard-{q}.txt')
    assert len(rows)==len(expected) and {r[0]:r[1:] for r in rows}=={i:us for i,(us,L) in expected.items()}
    merged=numbers(a.source/f'combined-{q}.tsv')
    ids=[r[0] for r in merged]
    assert len(set(ids))==len(ids) and set(ids)<=set(expected)
    if a.complete:assert set(ids)==set(expected)
    for i,L,v,h in merged:
        assert L==expected[i][1] and v>=0 and h in (0,1)
    print(f'q={q}: {len(expected)} required, {len(ids)} certified rows, {sum(r[-1] for r in merged)} relaxed positives')
by_forest={forest(us):i for i,(us,L) in hard[5].items()}
assert len(by_forest)==len(hard[5])
mapped=[(by_forest[forest(tuple(map(int,shapes[i])))],L,n,h) for i,L,n,h in numbers(a.source/'q5-late.tsv')]
assert mapped==numbers(a.source/'q5-late-ids.tsv') and len(set(r[0] for r in mapped))==len(mapped)
print(f'{len(mapped)} older forest rows independently mapped to chronological IDs')

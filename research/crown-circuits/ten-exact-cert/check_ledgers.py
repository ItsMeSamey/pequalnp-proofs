"""Independently reconcile all archived numerical row IDs and hit flags."""
from collections import Counter,defaultdict
from pathlib import Path
import gzip
base=Path(__file__).resolve().parent
read=lambda p:[list(map(int,x.split())) for x in (base/p).read_text().splitlines()]
def stats(path, cols, hit):
    a=read(path);assert len({r[0] for r in a})==len(a) and all(not r[hit] for r in a)
    return len(a),sum(r[cols] for r in a)
assert stats('five/a5.tsv',3,1)==(703,5590625)
assert (base/'seven/seven-graph.log').read_text().strip()=='[((8, False), 990), ((9, False), 70)]'
F=(1<<64)-1
H=[sum(1<<w for w in range(64) if w>>j&1) for j in range(6)]
allids=defaultdict(set);hard=defaultdict(set)
with gzip.open(base/'six/canon.txt.gz','rt') as stream:
 for idx,line in enumerate(stream):
    u=list(map(int,line.split()))
    branches=[v&h for j,v in enumerate(u) for h in (H[j],F^H[j])]
    q=4-len(set(u)-set(branches)-{F});allids[q].add(idx)
    if q not in (2,3):continue
    atoms=[F]
    for b in branches:atoms=[piece for a in atoms for piece in (a&b,a&~b) if piece]
    if all(sum(not (v&a) for a in atoms)>2 for v in set(u)-{F}):hard[q].add(idx)
assert [len(allids[i]) for i in range(5)]==[16118,18089,6400,1027,85]
for q,nvis in [(0,16118),(1,1171903)]:
    a=[list(map(int,row.split()[:5])) for row in (base/f'six/six-q{q}.tsv').read_text().splitlines()]
    assert len(a)==len(allids[q]) and {r[0] for r in a}==allids[q]
    assert sum(r[3] for r in a)==nvis and len([r for r in a if r[4]])==6
    exact=read('six/six-exact-w4.tsv' if not q else 'six/six-actual-q1.tsv')
    need=allids[q] if not q else {r[0] for r in a if r[4]}
    assert len(exact)==len(need) and {r[0] for r in exact}==need and all(r[1]==0 for r in exact)
for q,n,vis in [(2,1657,1407266),(3,283,10203877)]:
    p=f'six/six-hard-q{q}.tsv'
    assert stats(p,2,3)==(n,vis)
    assert {r[0] for r in read(p)}==hard[q]
assert stats('six/six-forest.tsv',2,3)==(85,3493930)
print('all finite lower-bound ledgers reconcile')

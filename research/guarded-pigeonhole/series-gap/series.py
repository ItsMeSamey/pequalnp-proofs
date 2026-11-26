"""Test the opposite parity on the Boolean product of two rooted gap copies."""
import runpy
from pathlib import Path
import sys

audit=Path(__file__).resolve().parent
seed=runpy.run_path(str(audit/'rooted-bipartite-gap.py'))
pc=runpy.run_path(str(audit/'rooted-hull.py'))
graph=seed['graph']; n=len(graph)
weight=seed['weight']
rows=graph+[r<<n for r in graph]
# Series cross-edges replace the two individual root edges.
for i,j in ((0,1),(n,n+1),(1,n),(0,n+1)):
    rows[i] ^= 1<<j
    rows[j] ^= 1<<i
assert all((rows[i]>>j&1)==(rows[j]>>i&1) for i in range(2*n) for j in range(2*n))
# For a sound lower bound, grant both intermediate pins for free.
equations=[(1<<v,1) for v in (0,1,n,n+1)]+[(weight|(weight<<n),1)]
k,forms=pc['forms'](2*n,equations)
pairs=[(f,pc['xor_forms'](r,forms)) for f,r in zip(forms,rows)]
print('Free variables',k,flush=True)
for degree in (2,3):
    # A NO system can derive affine facts without immediately refuting; do
    # not use the early stop of affine_closure based on affine dimension.
    from collections import deque
    index,low,images=pc['ring'](k,degree)
    work=deque()
    for a,b in pairs:
        poly=0
        for i in range(k+1):
            if a>>i&1:
                for j in range(k+1):
                    if b>>j&1:
                        poly ^= 1<<index[((1<<i)>>1)|((1<<j)>>1)]
        work.append(poly)
    basis={}
    while work:
        p=pc['reduce'](work.popleft(),basis)
        if not p: continue
        lead=p.bit_length();basis[lead]=p
        if lead==1:break
        if lead<=low:
            for m in images: work.append(pc['mul'](p,m))
    print('degree',degree,'rank',len(basis),'refutes',1 in basis,flush=True)

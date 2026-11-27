"""Six four-cycle phases. Literal marks are reused across parity clauses."""
from itertools import combinations,product
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from read_two_ring_nonzero import compile_nonzero
from ring_image_affine_phases import decide


def verify(charge):
    edge=list(combinations(range(4),2))
    rows=[]
    for i in range(6):
        for j in range(4):
            a,b=4*i+1+j,4*i+1+(j+1)%4
            rows.extend(((a,b),(-a,-b)))
    for v in range(4):
        ids=[i for i,e in enumerate(edge) if v in e]
        for bits in product(range(2),repeat=3):
            if sum(bits)%2!=charge[v]:
                rows.append(tuple(4*i+1+x for i,x in zip(ids,bits)))
    r=compile_nonzero(24,rows)
    ans=decide(*(r[k] for k in ('n','clauses','point','k')))
    if sum(charge)%2:
        assert ans['status']=='zero'
    else:
        assert ans['status']=='nonzero'
        w=ans['assignment']
        assert all(any(w[abs(l)-1]==(l>0) for l in c) for c in rows)


if __name__=='__main__':
    verify([0,0,0,0])
    verify([1,0,0,0])
    print('K4 physical even/odd phase verdicts and original satisfying word passed.')

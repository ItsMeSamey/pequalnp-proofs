"""Native OR/COPY contractions with four-slot packets on small examples."""
import mpmath as mp
from itertools import product
from math import prod
from random import Random


def evaluate(rows,t):
    occ = [x for row in rows for x in row]
    M=2*len(occ)
    # Exact polynomial quotient, including removable poles at samples in the grid.
    K={d: prod(t-r for r in range(-4,4) if r!=d)/prod(-r for r in range(-4,4) if r)
       for d in range(-3,4)}
    result=0
    for word in product((0,1), repeat=len(occ)):
        X=[x for x in word for _ in range(2)]
        v=[sum(K[j-i]*X[j] for j in range((i//4)*4,min(M,(i//4+1)*4))) for i in range(M)]
        value=1
        offset=0
        for row in rows:
            value*=1-prod(1-v[2*(offset+k)+1] if x>0 else v[2*(offset+k)+1]
                          for k,x in enumerate(row))
            offset+=len(row)
        for name in set(map(abs,occ)):
            vals=[v[2*i] for i,x in enumerate(occ) if abs(x)==name]
            assert len(vals)<=3
            value*=prod(vals)+prod(1-x for x in vals)
        result+=value
    return result

if __name__=='__main__':
    mp.mp.dps=70
    rng=Random(858)
    for rows in [((1,),),((1,),(-1,)),((1,2),(-1,)),((1,2),(-1,-2))]:
        expected=sum(all(any(bool(w>>(abs(x)-1)&1)==(x>0) for x in row) for row in rows)
                     for w in range(1<<max(abs(x) for row in rows for x in row)))
        N=64
        value=0j
        for j in range(N):
            root=mp.expj(2*mp.pi*j/N)
            value+=(evaluate(rows,1+2*root)+rng.choice((-.05,.05)))*sum(
                (-1/(2*root))**k for k in range(N))/N
        assert abs(value-expected)<.125,(rows,value,expected)
        print(expected,abs(value-expected))

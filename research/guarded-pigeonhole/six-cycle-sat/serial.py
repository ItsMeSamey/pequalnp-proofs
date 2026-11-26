from itertools import product
from runpy import run_path
from pathlib import Path
base=run_path(str(Path(__file__).with_name('check.py')))
decide,sat=base['decide'],base['sat']

def serial(n,clauses):
    assert clauses
    start=finish=sum(1<<(3*i) for i in range(n))
    w=3*n
    z=w+3*len(clauses)
    start |= 1<<z
    finish |= 1<<(z+3*len(clauses))
    gates=[(3*i,3*i+1,3*i+2) for i in range(n)]
    for h,clause in enumerate(clauses):
        j=w+3*h
        start |= 1<<j
        finish |= 1<<j
        gates += [(j,j+1,j+2)]*2
        for q,l in enumerate(clause):
            u=z+3*h+q
            false=3*(abs(l)-1)+int(l>0)
            gates.extend([(j+q,false,u+1),(false,u,u+1)])
        gates += [(j,j+2,j+1)]*2
    gates += [(3*i,3*i+2,3*i+1) for i in range(n)]
    return z+3*len(clauses)+1,start,finish,gates

universe=list(product(*[(i,-i) for i in (1,2,3)]))
for mask in range(1,256):
    clauses=[c for i,c in enumerate(universe) if mask>>i&1]
    network=serial(3,clauses)
    assert (network[1]^network[2]).bit_count()==2
    assert decide(network)==sat(3,clauses)
print('255 complete Hamming-distance-two SAT/UNSAT controls passed')

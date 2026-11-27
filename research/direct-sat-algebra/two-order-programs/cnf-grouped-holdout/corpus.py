"""Fixed holdout independent of solver implementation."""
from itertools import product, combinations
import random

def forbidden(scope,bits):
    return [(-v if b else v) for v,b in zip(scope,bits)]

def table(scope,pred):
    return [forbidden(scope,b) for b in product(range(2),repeat=len(scope)) if not pred(b)]

def corpus():
    for seed in (39071,39509):
        rng=random.Random(seed)
        def emit(name,n,rows):
            # Multiplicity and literal order vary without changing the relation.
            rows=[list(r) for r in rows]
            rows+= [r.copy() for r in rng.sample(rows,max(1,len(rows)//5))]
            sigma=list(range(1,n+1))
            rng.shuffle(sigma)
            for r in rows:
                r[:]=[sigma[abs(v)-1]*(1 if v>0 else -1) for v in r]
                rng.shuffle(r)
            rng.shuffle(rows)
            return f'{name}-{seed}',n,rows
        for n in (6,10):
            for planted in (False,True):
                w=[rng.randrange(2) for _ in range(n)]
                rows=[]
                while len(rows)<round(4.35*n):
                    sc=rng.sample(range(1,n+1),3)
                    b=tuple(rng.randrange(2) for _ in sc)
                    if not planted or any(w[v-1]!=z for v,z in zip(sc,b)):
                        rows.append(forbidden(sc,b))
                yield emit(f'random-{n}-{planted}',n,rows)
        for graph,edges in [('K4',list(combinations(range(4),2))),('K33',[(i,j) for i in range(3) for j in range(3,6)]),('wheel',[(0,i) for i in range(1,6)]+[(i,1+i%5) for i in range(1,6)])]:
            nv=max(max(e) for e in edges)+1
            charges=[rng.randrange(2) for _ in range(nv-1)]
            for odd in (0,1):
                full=charges+[(sum(charges)+odd)%2]
                rows=[]
                for v,q in enumerate(full):
                    sc=[i+1 for i,e in enumerate(edges) if v in e]
                    rows+=table(sc,lambda b:sum(b)%2==q)
                yield emit(f'{graph}-odd{odd}',len(edges),rows)
        for bad in (0,1):
            # Parity and one-in-three overlap; pair pins force the interface.
            rows=table([1,2,3],lambda b:sum(b)==1)
            rows+=table([3,4,5],lambda b:sum(b)%2==0)
            rows += [[-1],[-2],[-4],[(-5 if bad else 5)]]
            yield emit(f'mixed-pinned-{bad}',5,rows)
            # Locally nonempty distributed relations with no pins.
            rows=[]
            for i in range(8):
                rows+=table([1+i,1+(i+1)%8],lambda b:(b[0]^b[1])==(bad if i==7 else 0))
            yield emit(f'signed-ring-{bad}',8,rows)

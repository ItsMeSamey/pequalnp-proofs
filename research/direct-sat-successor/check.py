import json
from pathlib import Path
from random import Random
from successor import solve,portfolio,compile_cnf
from original_cnf import accepts_cnf

def fixture(d):
    size=1<<d
    n=d+2*size
    gates=[]
    def emit(a,b):
        gates.append((a,b))
        return 1<<(n+len(gates))
    values=[]
    for rail in range(2):
        row=[1<<(1+d+rail*size+i) for i in range(size)]
        for j in range(d):
            row=[a^emit(1<<(j+1),a^b) for a,b in zip(row[::2],row[1::2])]
        values.append(row[0])
    return n,gates,emit(*values)

def run():
    rng=Random(31829)
    for i in range(140):
        n=rng.randrange(6)
        g=[(rng.getrandbits(n+1+j),rng.getrandbits(n+1+j)) for j in range(rng.randrange(7))]
        y=rng.getrandbits(n+len(g)+1)
        models=[x for x in range(1<<n) if portfolio.evaluate(n,g,y,x)]
        for schedule,cap in [(('raw','normalized'),0),(('normalized','raw'),250000),((),100)]:
            result=solve(n,g,y,schedule=schedule,automata_budget=cap,routes=[],rewrite_budget=0)
            assert (result['status']=='sat')==bool(models)
            if models:assert result['witness'] in models
    for i in range(80):
        n=rng.randrange(1,6)
        cs=[[rng.randrange(1,n+1)*rng.choice([-1,1]) for _ in range(rng.randrange(4))]
            for _ in range(rng.randrange(12))]
        g,y=compile_cnf(n,cs)
        r=solve(n,g,y)
        models=[x for x in range(1<<n) if accepts_cnf(cs,x)]
        assert (r['status']=='sat')==bool(models)
        if models: assert r['witness'] in models
    # The raw automata stage declines, then D=2 collapses a distributive cancellation.
    g=[(2,4),(2,8),(2,12)]
    y=2 ^ 16 ^ 32 ^ 64
    r=solve(3,g,y,schedule=('raw','normalized'),automata_budget=0)
    assert r['route']=='normalized_affine' and r['witness']==1
    print('420 circuit invocations, 80 signed CNFs and ordered normalization rescue passed')
    for order in [('raw','normalized'),('normalized','raw')]:
        r=solve(*fixture(4),schedule=order)
        print(r['route'],r['cost']['attempts'][0]['cost']['charged_cells'],r['witness'])
        assert r['witness']==1048592 and r['verified']

if __name__=='__main__':run()

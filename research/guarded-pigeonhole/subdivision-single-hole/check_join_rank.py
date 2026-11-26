"""Compare iterative nonlinear-row reduction and exact Walsh counts with edge enumeration."""
import ast
from pathlib import Path
from itertools import combinations
from random import Random
source=Path(__file__).resolve().parent.parent/'subcubic-hot-cover'/'independent.py'
tree=ast.parse(source.read_text())
tree.body=[f for f in tree.body if isinstance(f,ast.FunctionDef) and f.name in {'affine','walsh','toggles'}]
exec(compile(tree,str(source),'exec'))
rng=Random(1684)
def parity(x):return x.bit_count()%2
def solve(n,constraints,tests):
    while True:
        A=affine(constraints,n)
        if A is None:return 0
        b,B=A; d=len(B); affine_rows=[]; piv={}; polys=[]
        for f in tests:
            c=f(b); l=[f(b^v)^c for v in B]
            p={1<<i for i in range(d) if l[i]}
            if c:p.add(0)
            for i,j in combinations(range(d),2):
                if f(b^B[i]^B[j])^l[i]^l[j]^c:p.add(1<<i|1<<j)
            while p and max(p,key=lambda x:(x.bit_count(),x)).bit_count()==2:
                k=max(p,key=lambda x:(x.bit_count(),x))
                if k not in piv:piv[k]=p;polys.append(p);break
                p=p^piv[k]
            else:
                if p:affine_rows.append((sum(p),int(0 in p)))
        if not affine_rows:
            W=0
            for h in range(1<<len(polys)):
                P=set()
                for j,p in enumerate(polys):
                    if h>>j&1:P^=p
                W+=walsh(P,d)
            assert W%(1<<len(polys))==0
            return W>>len(polys)
        tests=[lambda x,p=p:sum((x&m)==m for m in p)%2 for p in polys]
        n=d;constraints=affine_rows
for _ in range(600):
    n=rng.randrange(2,8); E=list(combinations(range(n),2)); rng.shuffle(E);E=E[:rng.randrange(min(len(E),10)+1)]
    q=len(E); planted=rng.randrange(1<<q)
    incidence=[sum(1<<i for i,e in enumerate(E) if v in e) for v in range(n)]
    constraints=[(m,parity(m&planted)) for m in incidence]
    if q and rng.randrange(2):constraints.append((1<<rng.randrange(q),rng.randrange(2)))
    tests=[lambda x,m=(1<<a|1<<b):int((x&m)==m) for a,b in combinations(range(q),2) if rng.randrange(5)==0]
    expected=sum(all(parity(m&x)==v for m,v in constraints) and not any(f(x) for f in tests) for x in range(1<<q))
    assert solve(q,constraints,tests)==expected
print('600 random edge hosts, exact counts agreed')

"""Safe-line measurement and marker projection on an alternating graph."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'fiber-switches'))
from completion import basis, chart, compose, dot, kernel, local, mv, solve

def project(A, L, z, sites, choices):
    n = len(A)
    E = [i for i in range(n) if i not in sites]
    m = len(E)
    mask = (1 << m) - 1
    ones = mask | (mask << m)
    def pack(x):
        return sum((x >> i & 1) << j for j,i in enumerate(E))
    def exterior(x):
        return pack(x) | (pack(mv(A,x)) << m)
    measured = [((1<<i,0),(A[i],0),(A[i]^(1<<i),1))[j] for i,j in zip(sites,choices)]
    equations = measured + [(r,z>>i&1) for i,r in enumerate(L)]
    x0 = solve(equations)
    if x0 is None:
        return None
    W = list(basis(exterior(x) for x in kernel([r for r,_ in measured],n)).values())
    assert len(W) == m
    B,T = chart(W,m)
    shear = [(1,3 if row>>i&1 else 2) for i,row in enumerate(B)]
    T = compose(shear,T)
    B = [row & ~(1<<i) for i,row in enumerate(B)]
    def transform(x):
        return local(exterior(x)^ones,T)^ones
    base = transform(x0)
    assert base>>m == mv(B,base&mask)
    rows = kernel([local(exterior(x),T)&mask for x in kernel([r for r,_ in equations],n)],m)
    assert len(rows) <= len(L)
    target = mv(rows,base&mask)
    def lift(u):
        if mv(rows,u) != target:
            return None
        constraints = list(equations)
        for j,(a,b) in enumerate(T):
            i = E[j]
            r = ((1<<i) if a&1 else 0) ^ (A[i] if a&2 else 0)
            constraints.append((r, (u>>j&1)^1^dot(a,3)))
        return solve(constraints)
    return B,rows,target,lift,transform,measured

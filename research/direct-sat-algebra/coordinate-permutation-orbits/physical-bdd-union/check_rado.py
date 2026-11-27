"""Independent canonical source, orbit enumeration, and original permutation replay."""
from itertools import combinations, product
from random import Random
from pathlib import Path
from types import SimpleNamespace
import sys
from orbit_rado import solve


def source(m):
    coords=[(i,j,t) for i,j in combinations(range(m),2) for t in range(4)]
    index={c:k for k,c in enumerate(coords)}
    R=[]; F=[]; start=0
    for k,(i,j,t) in enumerate(coords):
        a,b=sorted(((i+1)%m,(j+1)%m))
        R.append(index[a,b,(t%2)*2+t//2])
        F.append(index[i,j,t^int(i==0)])
        start|=int(t==0)<<k
    return tuple(R),tuple(F),start


def move(p,x):
    out=0
    while x:
        b=x&-x
        out|=1<<p[b.bit_length()-1]
        x-=b
    return out


def orbit(instance):
    R,F,start=instance
    q=[start]; seen={start}
    for x in q:
        for p in (R,F):
            y=move(p,x)
            if y not in seen:
                seen.add(y);q.append(y)
    return q


def check(instance,m,z,o,yes,**kw):
    result=solve(*instance,z,o,**kw)
    assert result['status']==('sat' if yes else 'unsat'),(m,z,o,result)
    if yes:
        R,F,x=instance
        inv=tuple(R.index(i) for i in range(len(R)))
        assert len(result['word'])<=2*m
        for j in result['word']:
            assert type(j) is int and 0<=j<2*m
            for _ in range(j):x=move(inv,x)
            x=move(F,x)
            for _ in range(j):x=move(R,x)
        assert not x&z and x&o==o
    return result


def four_color(m,E,forbidden):
    colors=[0];attempts=0
    def visit():
        nonlocal attempts
        v=len(colors)
        if v==m:return True
        for q in range(4):
            attempts+=1
            if any(colors[u]^q==forbidden for u in range(v) if (u,v) in E):continue
            colors.append(q)
            if visit():return True
            colors.pop()
        return False
    yes=visit()
    return yes,attempts


def main():
    inst=source(3); states=orbit(inst)
    assert len(states)==16
    R,F,start=inst
    assert solve(R,F,start^1,0)['status']=='skip'
    assert solve(tuple(reversed(R)),F,start,0)['status']=='skip'
    for z,o,cap in ((-1,0,None),(1<<len(R),0,None),(0,-1,None),(0,0,-1)):
        try:solve(R,F,start,z,o,assignment_cap=cap)
        except ValueError:pass
        else:raise AssertionError('invalid mask or assignment cap accepted')
    for masks in product(range(16),repeat=3):
        z=sum(f<<(4*j) for j,f in enumerate(masks))
        check(inst,3,z,0,any(not x&z for x in states))
    for z,o in ((0,1),(1,1),(0,3),(16,257),(34,273)):
        check(inst,3,z,o,any(not x&z and x&o==o for x in states))
    rng=Random(2041)
    inst=source(5);states=orbit(inst)
    assert len(states)==256
    for _ in range(24):
        z=sum(rng.choice((0,1,3,4,5,6,7,8,12))<<(4*j) for j in range(10))
        o=(1<<rng.randrange(40)) if rng.randrange(2) else 0
        check(inst,5,z,o,any(not x&z and x&o==o for x in states))
    for m in (7,9):
        inst=source(m)
        E=set(combinations(range(5),2))|{(i,i+1) for i in range(4,m-1)}
        for f in (0,2):
            z=sum(1<<(4*j+f) for j,e in enumerate(combinations(range(m),2)) if e in E)
            yes,attempts=four_color(m,E,f)
            assert yes==(f!=0)
            r=check(inst,m,z,0,yes)
            sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'orbit-color-frontier'))
            from cycle_syndrome import solve as cycle_solve
            raw=SimpleNamespace(rotation=inst[0],flip=inst[1],start=inst[2],zero=z)
            cycle=cycle_solve(raw)
            assert (cycle is not None)==yes
            # The standard graphic/dual connectivity value equals both
            # subgraph graphic ranks minus their union rank.
            def rank(edges):
                parent=list(range(m))
                def root(v):
                    while v!=parent[v]:v=parent[v]
                    return v
                k=0
                for u,v in edges:
                    a,b=root(u),root(v)
                    if a!=b:parent[a]=b;k+=1
                return k
            edges=sorted(E)
            lam=max(rank(edges[:i])+rank(edges[i:])-rank(edges) for i in range(len(edges)+1))
            assert lam==3
            print('cycle baseline lambda',lam,'SAT',yes)
            print('K5+path',m,f,attempts,r['cost'])
            if not yes:assert solve(*inst,z,assignment_cap=0)['status']=='skip'
    print('4096 exhaustive three-pair zero patterns, five one-pin controls, 24 five-vertex pin patterns')

if __name__=='__main__':main()

"""Uniform four-entry local tables for quotient-coordinate planes."""
from itertools import product
from collections import Counter
from clause_triangles import insert,rem,solve_rows,dot
from triangle_symbolic import sat2

def plan(blocks,U):
    zero={}
    for w in U:
        if not rem(zero,w,0)[0]: return None
        insert(zero,w,0)
    planes=[]; weights=Counter()
    for block in blocks:
        p={0}
        for w in block:
            a=rem(zero,w,0)[0]
            p|={x^a for x in p}
            if len(p)>4: return None
        planes.append(p); weights.update(p-{0})
    rows={}; selected=[]
    for w in sorted(weights,key=lambda x:(-weights[x],x)):
        if rem(rows,w,0)[0]:
            insert(rows,w,0); selected.append(w)
    bases=[[j for j,w in enumerate(selected) if w in p] for p in planes]
    if any((1<<len(ids))!=len(p) for ids,p in zip(bases,planes)): return None
    return selected,bases

def query(blocks,counts,y,U):
    layout=plan(blocks,U)
    if layout is None: raise ValueError('outside simultaneously coordinate binary planes')
    selected,bases=layout
    for fixed in product((0,1),repeat=len(U)):
        base={}
        for w,b in zip(U,fixed): insert(base,w,b)
        clauses=[]
        for block,cs,ys,ids in zip(blocks,counts,y,bases):
            for t in product((0,1),repeat=len(ids)):
                eq=dict(base)
                for j,b in zip(ids,t): insert(eq,selected[j],b)
                x=solve_rows(eq)
                z=[dot(w,x)^s for w,s in zip(block,ys)]
                legal=all(c or not p for c,p in zip(cs,z[1:])) and (
                    not z[0] or any(c>p for c,p in zip(cs,z[1:])))
                if not legal: clauses.append([(j,1-b) for j,b in zip(ids,t)])
        t=sat2(len(selected),clauses)
        if t is not None:
            for j,w in enumerate(selected): assert insert(base,w,t>>j&1)
            return solve_rows(base)
    return None

if __name__=='__main__':
    from random import Random
    rng=Random(1219); yes=no=outside_old=0
    from symbolic_dense import independent,split_forms
    for case in range(400):
        n=rng.randrange(4,8); basis=[]
        while len(basis)<n:
            v=rng.randrange(1<<n)
            if independent(basis+[v]):basis.append(v)
        U=basis[:1]; blocks=[]; y=[]; counts=[]
        for j in range(rng.randrange(1,7)):
            a,b=rng.sample(basis[1:],2)
            w=[(v^rng.choice([0,U[0]])) for v in (a,b,a^b)]
            blocks.append(w)
            counts.append([rng.randrange(3),rng.randrange(3)])
            y.append([rng.randrange(2) for _ in w])
        assert plan(blocks,U) is not None
        outside_old+=split_forms(blocks,U) is None
        def fits(x):
            for block,cs,ys in zip(blocks,counts,y):
                z=[dot(w,x)^s for w,s in zip(block,ys)]
                if any(not c and p for c,p in zip(cs,z[1:])):return False
                if z[0] and not any(c>p for c,p in zip(cs,z[1:])):return False
            return True
        x=query(blocks,counts,y,U)
        assert (x is not None)==any(fits(z) for z in range(1<<n))
        if x is None: no+=1
        else: assert fits(x); yes+=1
    print('plane charts',yes,no,'failed stricter distinct-remainders test',outside_old)

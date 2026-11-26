"""Compare primal grid connectivity with oriented boundary windings and seams."""
from itertools import product,combinations
from math import pi,cos,prod

def boundaries(cells):
    arcs=set()
    for x,y in cells:
        corners=[(x,y),(x+1,y),(x+1,y+1),(x,y+1)]
        for a,b in zip(corners,corners[1:]+corners[:1]):
            if (b,a) in arcs:
                arcs.remove((b,a))
            else:
                arcs.add((a,b))
    succ=dict(arcs)
    assert len(succ)==len(arcs)
    loops=[]
    while succ:
        v=next(iter(succ))
        path=[v]
        while v in succ:
            v=succ.pop(v)
            path.append(v)
        assert path[0]==path[-1]
        loops.append(list(zip(path,path[1:])))
    return loops

def wind(edges,p):
    x,y=p
    return sum((b[1]>a[1])-(a[1]>b[1]) for a,b in edges
               if a[0]==b[0] and a[0]>x+.25 and min(a[1],b[1])<y+.25<max(a[1],b[1]))

def check(w,h):
    vs=list(product(range(0,4*w,4),range(0,4*h,4)))
    es=[(u,v) for u,v in combinations(vs,2) if abs(u[0]-v[0])+abs(u[1]-v[1])==4]
    for mask in range(1<<len(es)):
        cells=set(vs)
        components=[{v} for v in vs]
        for i,(u,v) in enumerate(es):
            if mask>>i&1:
                for j in range(5):
                    cells.add(tuple((a*(4-j)+b*j)//4 for a,b in zip(u,v)))
                joined=set.union(*(c for c in components if u in c or v in c))
                components=[c for c in components if c.isdisjoint(joined)]+[joined]
        loops=boundaries(cells)
        for u,v in combinations(vs,2):
            diffs=[wind(loop,u)-wind(loop,v) for loop in loops]
            assert all(abs(d)<=1 for d in diffs)
            assert (not any(diffs)) == any(u in c and v in c for c in components)
            rotations=[1 if sum(a[0]*b[1]-a[1]*b[0] for a,b in loop)>0 else -1 for loop in loops]
            spherical=[rot-2*wind(loop,v) for rot,loop in zip(rotations,loops)]
            assert all(abs(rot)==1 and (d==0 or d==rot) for rot,d in zip(spherical,diffs))
            twisted=prod(2*cos(pi*(2*rot+d)/6) for rot,d in zip(spherical,diffs))
            assert abs(twisted-int(not any(diffs)))<1e-10
            # Trace with orientation fugacity 1 (2 each) and seam twist i,-i.
            numer=1
            for d in diffs:
                numer*=round(((1j)**d+(1j)**(-d)).real)
            assert numer==(2**len(loops))*int(not any(diffs))
    return (1<<len(es))*len(list(combinations(vs,2)))

print(check(3,2),'terminal-pair/configurations passed on the rectangular grid')

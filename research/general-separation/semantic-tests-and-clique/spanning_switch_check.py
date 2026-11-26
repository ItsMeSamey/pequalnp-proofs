"""Check component marking by the companion and its inverse on disk boundaries."""
from itertools import product,combinations
from math import prod
from plane_medial_loop_check import boundaries,wind

def mul(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
vs=list(product(range(0,12,4),range(0,8,4)))
es=[(a,b) for a,b in combinations(vs,2) if sum(abs(x-y) for x,y in zip(a,b))==4]
for mask in range(1<<len(es)):
    cells=set(vs)
    cc=[{v} for v in vs]
    for i,(a,b) in enumerate(es):
        if mask>>i&1:
            cells.update(tuple((x*(4-j)+y*j)//4 for x,y in zip(a,b)) for j in range(5))
            joined=set.union(*(c for c in cc if a in c or b in c))
            cc=[c for c in cc if not c&joined]+[joined]
    loops=boundaries(cells)
    for root in vs:
        rho=[(1 if sum(a[0]*b[1]-a[1]*b[0] for a,b in loop)>0 else -1)
             -2*wind(loop,root) for loop in loops]
        assert set(rho)<={-1,1} and rho.count(1)==len(cc)-1
        for u in (0,2,-1):
            a=[[0,0,1],[1,0,-1],[0,1,u]]
            b=[[1,1,0],[-u,0,1],[1,0,0]]
            assert mul(a,b)==mul(b,a)==[[1,0,0],[0,1,0],[0,0,1]]
            assert prod(sum(m[i][i] for i in range(3)) for m in (a if r==1 else b for r in rho))==u**(len(cc)-1)
print('768 rooted configurations and 2304 companion trace products passed')

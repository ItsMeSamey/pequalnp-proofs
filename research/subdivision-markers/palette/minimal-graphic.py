from itertools import combinations
from classify import calculate,dual_material,lib
from finite import sid
def skeleton(cols):
    coords={i:i for i in range(8)}
    for a in cols:
        if a not in coords:
            bit=len(coords)
            coords.update({v^a:q^bit for v,q in list(coords.items())})
    cols=[coords[a] for a in cols]
    r=(len(coords)-1).bit_length()
    edges={v for v in range(1,1<<r) if v.bit_count()<=2}
    def solve(im):
        if any(v<len(im) and im[v] not in edges for v in cols):return False
        if len(im)==1<<r:return True
        return any(solve(im+[v^a for v in im]) for a in edges-set(im))
    return solve(list(range(8)))
ncheck=0
for n in range(3,7):
    for cols in combinations(range(1,16),n):
        p=calculate(cols)
        if p not in lib or len(lib[p])!=n:continue
        for O in (list(cols),dual_material(list(cols))):
            p=calculate(O)
            if p>>sid[frozenset([0,7])]&1: continue
            ncheck+=1
            if not skeleton(O):
                print('nongraphic minimum',p,O,'original',cols,flush=True)
                raise SystemExit
print('tested',ncheck,'no failure')

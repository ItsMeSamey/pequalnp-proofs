from itertools import combinations,product
from random import Random
rng=Random(773)
def cf(F,assignment):
    return {tuple((i,b) for i,b in term if i not in assignment) for term in F if all(i not in assignment or assignment[i]==b for i,b in term)}
def obstruction(F,A):
    edges={(tuple(v for v in term if v[0] in A),tuple(v for v in term if v[0] not in A)) for term in F}
    edges={(p,q) for p,q in edges if p and q}
    for p,r in combinations({p for p,q in edges},2):
        for q,s in combinations({q for p,q in edges},2):
            if (int((p,q) in edges)*int((r,s) in edges)-int((p,s) in edges)*int((r,q) in edges))%3:
                guards=set()
                for x,y in product((p,r),(q,s)):
                    pat=set(x+y)
                    if (x,y) in edges:guards.update(i for i,b in pat)
                    else:
                        for term in F:
                            if pat<set(term): guards.add(min(set(term)-pat)[0])
                return guards
    return None
def failing(F,S,trees):
    for bits in product((0,1),repeat=len(S)):
        g=cf(F,dict(zip(S,bits)))
        total=set()
        for tree in trees:
            obs=next((z for cut in tree if (z:=obstruction(g,cut)) is not None),None)
            if obs is None:break
            total|=obs
        else:return total
    return None
for _ in range(120):
    n=6
    F={tuple(sorted((i,rng.randrange(2)) for i in rng.sample(range(n),rng.randrange(2,5)))) for _ in range(10)}
    trees=[]
    for j in range(2):
        v=rng.sample(range(n),n)
        trees.append([set(v[:h]) for h in range(1,n)])
    def search(S):
        bad=failing(F,S,trees)
        if bad is None:return True
        if len(S)==2:return False
        return any(search(S+(v,)) for v in bad)
    truth=any(failing(F,S,trees) is None for k in range(3) for S in combinations(range(n),k))
    assert search(())==truth
print('120 exact rank-one selector searches matched exhaustive selectors')

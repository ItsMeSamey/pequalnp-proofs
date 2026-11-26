from itertools import combinations,product
from random import Random

def matching(clauses):
    owner={}
    def take(i,seen):
        for v,sign in clauses[i]:
            if v in seen: continue
            seen.add(v)
            if v not in owner or take(owner[v],seen):
                owner[v]=i
                return True
        return False
    if not all(take(i,set()) for i in range(len(clauses))):return None
    return {i:v for v,i in owner.items()}

def circuit_test(clauses,p,n):
    arcs=[[] for _ in range(n)]
    for i,c in enumerate(clauses):
        v=p[i]; sv=dict(c)[v]
        arcs[v]=[(w,1^sv^s) for w,s in c if w!=v]
    good={v for v,d in enumerate(arcs) if not d}
    for start in range(n):
        def visit(v,seen,par):
            for w,s in arcs[v]:
                if w==start and par==s:return True
                if w not in seen and visit(w,seen|{w},par^s):return True
            return False
        if visit(start,{start},0):good.add(start)
    for _ in range(n):
        good.update(v for v,d in enumerate(arcs) if any(w in good for w,s in d))
    return len(good)==n

def brute(clauses,n):
    return any(all(len({(a>>v&1)^s for v,s in c})>1 for c in clauses) for a in range(1<<n))

if __name__=='__main__':
    rng=Random(75); checked=0
    for _ in range(900):
        n=rng.randint(3,9)
        # Complementary transversal is the cycle through all n vertices.
        clauses=[]; pairs=[]
        for u in range(n):
            v=(u+1)%n
            w=rng.choice([w for w in range(n) if w not in (u,v)])
            f,g=rng.randrange(2),rng.randrange(2)
            pairs.append((u,v,w,f,g))
            clauses.append([(u,0),(v,1^f),(w,1^g)])
        p=matching(clauses)
        assert p is not None
        answer=circuit_test(clauses,p,n)
        direct=any(all(not (((a>>u)^(a>>v)^f)&1 and ((a>>u)^(a>>w)^g)&1) for u,v,w,f,g in pairs) for a in range(1<<n))
        assert answer==direct==brute(clauses,n)
        checked+=1
    # An unsatisfiable signed-free Fano plane has a full pivot matching.
    c=[[(i-1,0),(j-1,0),((i^j)-1,0)] for i,j in combinations(range(1,8),2) if i^j>j]
    assert not circuit_test(c,matching(c),7) and not brute(c,7)
    print(checked,'cographic tests and Fano rejection passed')

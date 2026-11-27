from itertools import combinations, permutations, product
from random import Random
from sparse_cap_solver import solve, join, nae_witness
rng=Random(740)
tests=positives=0
for n in (2,3,4,5):
    perms=list(permutations(range(n)))
    sparse=[p for p in perms if sum(i!=x for i,x in enumerate(p)) in (2,3)]
    tables=([list(compress) for k in range(len(sparse)+1) for compress in combinations(sparse,k)]
            if n<=3 else [rng.sample(sparse,rng.randrange(len(sparse)+1)) for _ in range(90)])
    for table in tables:
        g=rng.choice(perms)
        H=[[g[x] for x in row] for row in table]
        for marks in [None,*combinations(range(n),2)]:
            result=solve(g,H,marks)
            pairs=[marks] if marks is not None else list(combinations(range(n),2))
            def good(k,r,s):
                return join(k,g,r,s) and not any(join(k,h,r,s) for h in H)
            truth=any(good(k,r,s) for r,s in pairs for k in perms)
            if bool(result)!=truth or (truth and not good(result[0],*result[1])):
                raise RuntimeError((g,H,marks))
            tests+=1
            positives+=truth
print(tests,'cap queries;',positives,'positive')
cases=0
for _ in range(200):
    C=[tuple(rng.choice((-3,-2,-1,1,2,3)) for _ in range(3)) for j in range(rng.randrange(1,6))]
    truth=any(all(len({bits[abs(x)-1]^(x<0) for x in c})==2 for c in C) for bits in product((0,1),repeat=3))
    if bool(nae_witness(C))!=truth:raise RuntimeError(C)
    cases+=1
print(cases,'NAE instances')

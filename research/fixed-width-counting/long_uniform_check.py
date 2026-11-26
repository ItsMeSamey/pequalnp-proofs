from itertools import combinations, product

def all_count(n, clauses):
    return sum(all(any(((bits >> (abs(l)-1)) & 1) == (l>0) for l in c) for c in clauses)
               for bits in range(1 << n))

def check(n, clauses, W):
    padded_full = [c+tuple(range(n+1,n+1+W-len(c))) for c in clauses]
    guards = tuple(range(n+1, n+W+1))
    assert all_count(n+W, padded_full) - all_count(n+W, padded_full+[guards]) == all_count(n, clauses)
    known = {j: 2**n for j in range(n+1, W+1)}
    for s in range(n,0,-1):
        kept = [c for c in clauses if len(c)>=s]
        padded = [c+tuple(range(n+1,n+1+W-len(c))) for c in kept]
        assert all(len(c)==W for c in padded)
        H, rem = divmod(all_count(n+W,padded),2**s)
        assert rem==0
        known[s] = H-sum((1 << (k-s-1))*known[k] for k in range(s+1,W+1))
        assert known[s] == all_count(n,kept)
    return known[1]

if __name__ == '__main__':
    cases=0
    for n in (1,2,3):
        universe=[tuple((i+1)*s for i,s in enumerate(signs) if s) for signs in product((-1,0,1),repeat=n) if any(signs)]
        for count in range(3):
            for formula in combinations(universe,count):
                for W in (n,n+1,n+2):
                    assert check(n,formula,W)==all_count(n,formula)
                    cases+=1
    print(cases,"uniform-width reductions passed")

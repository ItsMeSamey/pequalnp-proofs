from random import Random
from itertools import combinations,permutations
from functools import lru_cache
from boolean_value_automata import apply,dot
from two_order_intervals import solve,tree

def value(p,order,x):
    row=p[1]
    for i,v in enumerate(order):row=apply(row,p[2][i][x>>v&1])
    return dot(row,p[3])

if __name__=='__main__':
    rng=Random(833)
    for n in range(1,6):
        for perm in permutations(range(n)):
            @lru_cache(None)
            def rec(a,b,k):
                xs=sorted(perm.index(i) for i in range(a,b))
                if xs[-1]-xs[0]!=b-a-1:return False
                if b-a==1:return True
                for t in range(1,min(k,b-a)):
                    for cuts in combinations(range(a+1,b),t):
                        path=(a,)+cuts+(b,)
                        if all(rec(i,j,k) for i,j in zip(path,path[1:])):return True
                return False
            for k in (2,3,4):
                assert ((0,n) in tree(tuple(range(n)),perm,k))==rec(0,n,k)
    for _ in range(160):
        n=rng.randrange(8); orders=[list(range(n)),list(range(n))]
        for order in orders:rng.shuffle(order)
        def program():
            w=[rng.randrange(1,4) for i in range(n+1)]
            return w,rng.getrandbits(w[0]),[tuple(tuple(rng.getrandbits(b) for j in range(a)) for bit in range(2)) for a,b in zip(w,w[1:])],rng.getrandbits(w[-1])
        p,q=program(),program()
        result=solve(p,orders[0],q,orders[1],arity_cap=max(2,n))
        models=[x for x in range(1<<n) if value(p,orders[0],x) and value(q,orders[1],x)]
        assert result['status']==('sat' if models else 'unsat')
        if models:assert result['witness'] in models
    p=([1]*5,1,[((1,),(1,))]*4,1)
    for o in ([3,2,1,0],[1,3,0,2]):
        for k in (2,4):
            r=solve(p,list(range(4)),p,o,arity_cap=k)
            print(o,k,r['status'],r['cost'])

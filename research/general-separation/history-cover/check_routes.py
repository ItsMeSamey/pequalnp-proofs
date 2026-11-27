from cnf_routes import solve_cnf
from random import Random
from collections import Counter
r=Random(826); routes=Counter()
for n in range(1,8):
    for _ in range(100):
        cls=[[r.choice([-1,1])*r.randint(1,n) for _ in range(r.choice([1,2,3]))] for _ in range(r.randrange(15))]
        expected=any(all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cls) for x in range(1<<n))
        for width in (0,2,5):
            w,route=solve_cnf(n,cls,width=width)
            assert (w is not None)==expected
            routes[route]+=1
print(routes)

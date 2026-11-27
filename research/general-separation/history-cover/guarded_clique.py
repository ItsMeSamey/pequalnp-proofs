from itertools import combinations
from cnf_routes import solve_cnf,width_order
for n in (6,12,32,80):
    cls=[(-1,-i,-j) for i,j in combinations(range(2,n+2),2)]
    assert width_order(n+1,cls,4) is None
    w,route=solve_cnf(n+1,cls,width=4,backdoor=1)
    assert w is not None and route=='2SAT backdoor'
    print(n,len(cls),route)

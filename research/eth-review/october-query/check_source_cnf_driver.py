from itertools import product
from source_cnf_driver import count
cases=[(0,[]),(2,[]),(2,[[]]),(2,[[1,-1]]),(2,[[1]]),(2,[[1],[-1]]),
       (3,[[-2,1],[2]]),(2,[[1,1],[2,-1]]),(3,[[3],[3],[3]]),
       (2,[[1],[1],[1],[1]])]
for n,c in cases:
    truth=sum(all(any(x[abs(l)-1]==int(l>0) for l in clause) for clause in c) for x in product((0,1),repeat=n))
    assert count(n,c)==truth,(n,c)
print('10 original fixed-density counts matched, including unused and repeated occurrences')

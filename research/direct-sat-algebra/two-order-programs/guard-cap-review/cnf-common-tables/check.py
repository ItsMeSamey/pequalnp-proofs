from itertools import product
from random import Random
from route import solve,affine,horn,binary
def encode(s,vals):
    return [tuple(-v if x>>i&1 else v for i,v in enumerate(s)) for x in range(1<<len(s)) if x not in vals]
def accepts(rows,x):
    return all(any(bool(x&(1<<(abs(l)-1)))==(l>0) for l in r) for r in rows)
counts=[0,0,0]
for truth in range(1,256):
    vs=[x for x in range(8) if truth>>x&1]
    S=set(vs)
    ref=[all((a^b^c) in S for a,b,c in product(vs,repeat=3)),all((a&b) in S for a,b in product(vs,repeat=2)),all(((a&b)|(b&c)|(a&c)) in S for a,b,c in product(vs,repeat=3))]
    for j,fn in enumerate((affine,horn,binary)):
        assert (fn((0,1,2),vs) is not None)==ref[j]
        counts[j]+=int(ref[j])
    ans=solve(3,encode((1,2,3),S))
    assert (ans.status=="SAT")==any(ref)
    if ans.status=="SAT": assert ans.witness in S
assert solve(3,encode((1,2,3),[])).status=="UNSAT"
rng=Random(75213)
decisions=0
for _ in range(500):
    n=rng.randint(3,7); rows=[]
    for i in range(rng.randrange(1,8)):
        k=rng.randint(1,3); s=rng.sample(range(1,n+1),k); t=rng.randrange(1<<(1<<k))
        rows+=encode(s,[j for j in range(1<<k) if t>>j&1])
    ans=solve(n,rows)
    if ans.status=="SKIP": continue
    decisions+=1
    assert (ans.status=="SAT")==any(accepts(rows,x) for x in range(1<<n))
    if ans.status=="SAT": assert accepts(rows,ans.witness)
assert solve(6,encode((1,2,3),[0,3,5,6])+[(4,-5,-6)]).route=="NO_COMMON_CLASS"
assert solve(4,[(1,2,3,4)]).route=="ARITY"
assert solve(3,[(1,2,3)],max_cells=7).route=="CELL_CAP"
assert solve(0,[]).witness==0 and solve(0,[()]).status=="UNSAT"
print("all ternary tables checked; nonempty affine/meet/majority counts",counts,"; joint decisions",decisions,"of 500")

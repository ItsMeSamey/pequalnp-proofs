"""Independent matching-sign certificate test on K3,3, using finite sums."""
from itertools import combinations, permutations
from random import Random

def parity(x): return x.bit_count()%2
def assignment(t):
    a=[[(t>>(2*i+j))&1 for j in range(2)] for i in range(2)]
    for row in a: row.append(1^row[0]^row[1])
    a.append([1^a[0][j]^a[1][j] for j in range(3)])
    return sum(a[i][j]<<(3*i+j) for i in range(3) for j in range(3))
xs=[assignment(t) for t in range(16)]
inv_pairs=[(e,f) for e,f in combinations(range(9),2) if e//3 < f//3 and e%3 > f%3]
local=[(e,f) for e,f in combinations(range(9),2) if e//3==f//3 or e%3==f%3]
def table(pair):
    a,b=pair
    return sum(((x>>a)&(x>>b)&1)<<t for t,x in enumerate(xs))
def val(q,t): return q>>t&1
def polar(q):
    return sum((val(q,0)^val(q,1<<i)^val(q,1<<j)^val(q,(1<<i)^(1<<j)))<<k for k,(i,j) in enumerate(combinations(range(4),2)))
def rank(p):
    rows=[0]*4
    for k,(i,j) in enumerate(combinations(range(4),2)):
        if p>>k&1:
            rows[i]^=1<<j; rows[j]^=1<<i
    pivots={}
    for row in rows:
        while row:
            idx=row.bit_length()-1
            if idx not in pivots:
                pivots[idx]=row; break
            row^=pivots[idx]
    return len(pivots)
q=0
for pair in inv_pairs: q^=table(pair)
options={polar(q):(q,[])}
for pair in local:
    term=table(pair)
    for p,(old,certificate) in list(options.items()):
        options.setdefault(p^polar(term),(old^term,certificate+[pair]))
best=min(options,key=rank)
q,certificate=options[best]
r=rank(best)
assert r==2
terms={}
for ell in range(16):
    tform=sum((-1)**(val(q,t)^parity(ell&t)) for t in range(16))
    if not tform: continue
    assert abs(tform)==2**(4-r//2)
    s=next(s for s in range(512) if all(parity((xs[t]^xs[0])&s)==parity(ell&t) for t in range(16)))
    terms[s]=(1 if tform>0 else -1)*(-1)**parity(s&xs[0])
assert len(terms)==2**r
rng=Random(43)
for _ in range(100):
    w=[rng.randrange(32) for _ in range(9)]; perm=0; partial={s:0 for s in terms}
    for sigma in permutations(range(3)):
        mask=sum(1<<(3*i+sigma[i]) for i in range(3)); valprod=1
        for i,j in enumerate(sigma): valprod*=w[3*i+j]
        perm+=valprod
        inv=sum(sigma[i]>sigma[j] for i,j in combinations(range(3),2))
        for s in terms: partial[s]+=(-1)**(inv+parity(s&mask))*valprod
    lifted=sum(terms[s]*v for s,v in partial.items())%64
    assert (lifted//2)%32==perm%32
print("K3,3 rank",r,"conflicts",certificate,"signed forms",len(terms),"100 mod-32 checks passed")

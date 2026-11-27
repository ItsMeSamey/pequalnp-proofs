from lift import join,extend_horn,grouped
from random import Random
def valid(rows,w): return all(any(bool(w&(1<<(abs(l)-1)))==(l>0) for l in r) for r in rows)
def check(n,pre,tail,B,left,right,fixed=()):
    a=join(n,pre,tail,B,left,right,fixed=fixed)
    mask=sum(1<<(i-1) for i in B)
    W=[{w&mask for w in range(1<<n) if valid(pre,w) and valid([(l,) for l in p],w)} for p in (left,right)]
    T=[g for g in range(1<<n) if not any(g&(1<<(v-1)) for v in fixed) and all(
        all((x^sum(((g>>v)&1)<<i for i,v in enumerate(scope))) in bads for x in bads) for scope,bads in grouped(tail).items())]
    permitted={g for g in T if {w^(g&mask) for w in W[0]}==W[1]}
    if a.status!="SKIP":
        assert (a.status=="LIFT")==bool(permitted)
        if permitted:
            assert a.shift in permitted
            for w in W[0]:
                q=w^(a.shift&mask)
                args=[v if q>>(v-1)&1 else -v for v in B]
                assert extend_horn(n,pre,right,args) is not None
    return a
# Non-bijunctive Horn ternary shared with selector-derived implications.
pre=[(-2,-3,4),(1,-2,5),(-1,-2,-5)]
tail=[(-5,6),(5,-6)]
a=check(6,pre,tail,[2,3,4,5],[-1],[1]); assert a.status=="LIFT" and a.shift&48==48
assert check(6,pre,tail,[2,3,4,5],[-1],[1],[6]).status=="NO_GROUP_LIFT"
# Hidden Horn wire projected by resolvents; explicit empty and singleton cases.
assert check(4,[(1,2),(-1,-2),(-2,3),(-3,4)],[(4,)], [4],[-1],[1]).status=="NO_GROUP_LIFT"
assert check(2,[(1,2),(1,-2)],[],[],[-1],[1]).status=="NO_GROUP_LIFT"
assert check(2,[()],[],[],[-1],[1]).status=="LIFT"
assert join(6,pre,tail,[2,3,4,5],[-1],[1],cap=0).status=="SKIP"
rng=Random(84)
for _ in range(250):
    pre=[]; tail=[]
    for j in range(6):
        names=rng.sample([2,3,4,5],rng.randint(1,2))
        r=[-i for i in names]
        if rng.randrange(2): r[0]=-r[0]
        if rng.randrange(3): r.append(rng.choice([1,-1]))
        pre.append(tuple(r))
    for j in range(3):
        tail.append(tuple(rng.choice([-i,i]) for i in rng.sample([2,3,4,6],rng.randint(1,3))))
    check(6,pre,tail,[2,3,4],[-1],[1])
print("250 full original-CNF translation-oracle checks; non-bijunctive shift, pinned negative and empty boundary passed")

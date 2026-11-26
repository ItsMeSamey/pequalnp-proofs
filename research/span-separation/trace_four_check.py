from itertools import combinations
E=[16,18,24,27,32,36,40,45,48,54,56,63,8,9,10,11,12,13,14,15]
def add(s,v):
    return s | frozenset(i^v for i in s)
def family(e):
    all_s={frozenset({0})}
    for x in e: all_s.update([add(s,x) for s in all_s])
    return {frozenset(x for x in s if x<16) for s in all_s}
a,b=family(E),family(E+[1])
print(len(a),len(b), sorted(map(sorted,b-a)))
for v in range(1,16):
    for op in (lambda s:frozenset(min(x,x^v) for x in s), lambda s:frozenset(x for x in s if (x&v).bit_count()%2==0)):
        assert {op(s) for s in a}=={op(s) for s in b}
def orth(kernel):
    return frozenset(x for x in range(16) if all((x&y).bit_count()%2==0 for y in kernel))
def has(kernel):
    return any(i.bit_count()>=3 and all(j==0 or j==i or j&i!=j for j in kernel) for i in kernel)
good={s:has(s) for s in b|a}
from functools import lru_cache
@lru_cache(None)
def flags(s):return has(s),has(orth(s))
counts=[0,0,0]
for t in combinations(range(1,16),4):
    sums=[0]
    for x in t:sums += [x^y for y in sums]
    if len(set(sums))<16:continue
    def outcome(c):
        f=[flags(frozenset(j for j,x in enumerate(sums) if x in h)) for h in c]
        return tuple(map(any,zip(*f)))
    p,d=outcome(a)
    assert (p,d)==outcome(b)
    counts[0]+=1;counts[1]+=p;counts[2]+=d
print(counts)

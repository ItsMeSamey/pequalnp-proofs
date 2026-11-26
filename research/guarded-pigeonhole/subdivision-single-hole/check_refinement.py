"""Independent truth-table checks of stable-rank monotonicity on fiber products."""
import random


def span(generators):
    s={0}
    for v in generators:
        s.update([a^v for a in s])
    return s


def closure(points,rows,n):
    while points:
        def restrict(f):
            return sum(((f>>p)&1)<<i for i,p in enumerate(points))
        tests=span(restrict(f) for f in rows)
        affine=span([(1<<len(points))-1]+[
            sum(((p>>j)&1)<<i for i,p in enumerate(points)) for j in range(n)])
        constraints=tests&affine
        if constraints=={0}:return len(tests).bit_length()-1
        reject=0
        for c in constraints:reject|=c
        points=[p for i,p in enumerate(points) if not reject>>i&1]
    return None


def polynomial(rng,coords,n):
    terms=[()]+[(a,) for a in coords]+[(a,b) for j,a in enumerate(coords) for b in coords[:j]]
    enabled=[s for s in terms if rng.randrange(2)]
    return sum((sum(all(x>>j&1 for j in s) for s in enabled)%2)<<x for x in range(1<<n))


rng=random.Random(609)
n=5
points=list(range(1<<n))
for trial in range(550):
    left=[polynomial(rng,[0,1,2],n) for _ in range(rng.randrange(1,4))]
    right=[polynomial(rng,[0,3,4],n) for _ in range(rng.randrange(1,4))]
    parent=closure(points,left+right,n)
    for h in (0,1):
        fiber=[p for p in points if p&1==h]
        a=closure(fiber,left,n)
        b=closure(fiber,right,n)
        full=closure(fiber,left+right,n)
        if a is None or b is None:assert full is None
        else:assert parent is not None and a+b==full<=parent
print('1100 seeded refinements satisfied affine rejection, rank additivity and monotonicity.')

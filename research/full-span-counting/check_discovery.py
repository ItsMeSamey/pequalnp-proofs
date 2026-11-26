#!/usr/bin/env python3
"""Check conjunction recovery, repeated-tuple correlations, and isolated moments."""
from itertools import combinations, product
from random import Random


def sub(a,b):
    return a & b == a


def recover(m,rows):
    # (pattern, positive weight, discrepancy); unrestricted off the support.
    def energy(mask):
        return sum(h*err**2 for v,h,err in rows if sub(mask,v))
    total = energy(0)
    if total == 0:
        return None
    shared = sum(1 << i for i in range(m) if energy(1 << i) == total)
    weighted = sum(h*err for v,h,err in rows if sub(shared,v))
    weight = sum(h for v,h,_ in rows if sub(shared,v))
    assert weighted % weight == 0
    return shared,weighted//weight


def main():
    rng = Random(4975231)
    double_tests = 0
    for case in range(80):
        m = rng.randrange(2,7)
        hidden = rng.randrange(1, 1 << m)
        coefficient = rng.choice((-7,-2,1,5))
        scope = rng.sample(range(1,1 << m),rng.randrange(1,1 << m))
        rows = [(v,rng.choice((1,9,2**140+3)),coefficient*int(sub(hidden,v))) for v in scope]
        result = recover(m,rows)
        if result is None:
            assert not any(err for _,_,err in rows)
        else:
            term,c = result
            assert sub(hidden,term) and c == coefficient
            assert all(err == c*sub(term,v) for v,_,err in rows)
        # Signed residual weights need not have a single-term representation.
        data = [(v,rng.randint(-10,10)) for v in scope]
        for d in range(4):
            prefix = tuple(rng.randrange(m) for _ in range(rng.randrange(d+1)))
            allowed = rng.sample(range(m),rng.randrange(1,m+1))
            pmask = sum(1 << i for i in set(prefix))
            amask = sum(1 << i for i in allowed)
            left = 0
            for tail in product(allowed,repeat=d-len(prefix)):
                mask = pmask
                for i in tail:
                    mask |= 1 << i
                left += sum(a for v,a in data if sub(mask,v))**2
            right = sum(a*b*((v&w&amask).bit_count()**(d-len(prefix)))
                        for v,a in data for w,b in data if sub(pmask,v&w))
            assert left == right
            double_tests += 1
    needle = 0
    for m in range(2,7):
        for k in range(1,m+1):
            for tup in combinations(range(m),k):
                hidden = sum(1 << i for i in tup)
                baseline = [int(0 < v.bit_count() < k or (not v and k%2)) for v in range(1 << m)]
                perturbed = [h + ((-1)**(k-v.bit_count()) if sub(v,hidden) else 0)
                             for v,h in enumerate(baseline)]
                assert min(perturbed) >= 0 and baseline[0] != perturbed[0]
                for q in range(1 << m):
                    assert sum(b-a for v,(a,b) in enumerate(zip(baseline,perturbed)) if sub(q,v)) == int(q==hidden)
                needle += 1
    print(f"80 hidden-term supports, {double_tests} double-copy checks, {needle} isolated moments passed.")


if __name__ == "__main__":
    main()

"""Finite exact checks of reverse affine-support phase substitution."""
from collections import Counter
from itertools import product
from random import Random

# An affine form (mask,bias) is evaluated on ordinary GF(2) bits.
def affine(form, row):
    mask, bias = form
    return ((mask & row).bit_count() & 1) ^ bias


def monomials(table):
    coeff = list(table)
    n = (len(coeff) - 1).bit_length()
    for i in range(n):
        for mask in range(len(coeff)):
            if mask & (1 << i):
                coeff[mask] ^= coeff[mask ^ (1 << i)]
    return [mask for mask, bit in enumerate(coeff) if bit]


def degree(table):
    return max((mask.bit_count() for mask in monomials(table)), default=-1)


def rank(masks):
    basis = {}
    for mask in masks:
        while mask:
            p = mask.bit_length() - 1
            if p not in basis:
                basis[p] = mask
                break
            mask ^= basis[p]
    return len(basis)


def local_checks():
    forms = list(product(range(8), range(2)))
    kinds = Counter()
    for a, b, d in product(forms, repeat=3):
        tab = [affine(a,x)*affine(b,x)*affine(d,x) for x in range(8)]
        r = rank([a[0], b[0], d[0]])
        assert (degree(tab) == 3) == (r == 3)
        for x, abc in enumerate(tab):
            assert (-1)**abc == 1-2*abc
            av,bv,dv = [affine(form,x) for form in (a,b,d)]
            assert int(dv == av*bv) == int(av==0 and dv==0)+int(av==1 and dv==bv)
        kinds[r] += 1
    return dict(sorted(kinds.items()))


def reverse_count(q, gates, out, defer):
    # Test harness only: represents phases and supports by finite arrays.
    # Its enumerated row count is NOT the asymptotic algorithm's runtime.
    metrics = Counter()
    def solve(i, support, sign):
        metrics["nodes"] += 1
        if not any(support):
            return 0
        if i == 0:
            metrics["leaves"] += 1
            return sum(v for v,live in zip(sign,support) if live)
        a,b = gates[i-1]
        size = len(sign)//2
        projected = [support[x] or support[x+size] for x in range(size)]
        free = all(support[x] == support[x+size] for x in range(size))
        if not free:
            metrics["pinned"] += 1
            ans = 0
            for av in (0,1):
                ys = [av*affine(b,x) for x in range(size)]
                sub = [affine(a,x)==av and support[x+y*size] for x,y in enumerate(ys)]
                vals = [sign[x+y*size] for x,y in enumerate(ys)]
                ans += solve(i-1, sub, vals)
            return ans
        vals = [sign[x + affine(a,x)*affine(b,x)*size] for x in range(size)]
        # Conservative finite shortcut checks on the entire ambient cube.
        # A restricted support could additionally lower this degree.
        bits = [int(s == -1) for s in vals]
        terms = monomials(bits)
        d = max((mask.bit_count() for mask in terms), default=-1)
        primary_only = all(mask < (1<<q) for mask in terms if mask.bit_count() == 3)
        if d <= 2 or (defer and d <= 3 and primary_only):
            metrics["folded"] += 1
            return solve(i-1, projected, vals)
        metrics["signed"] += 1
        flag = [projected[x] and affine(a,x) and affine(b,x) and sign[x]!=sign[x+size] for x in range(size)]
        return solve(i-1, projected, sign[:size])-2*solve(i-1, flag, sign[:size])
    m=len(gates)
    domain=1<<(q+m)
    total=solve(m,[True]*domain,[(-1)**affine(out,x) for x in range(domain)])
    return ((1<<q)-total)//2, metrics


def brute(q,gates,out):
    count=0
    for x in range(1<<q):
        row=x
        for i,(a,b) in enumerate(gates):
            row |= (affine(a,row)*affine(b,row)) << (q+i)
        count += affine(out,row)
    return count


def main():
    print("Three-form checks by linear rank:",local_checks())
    rng=Random(513)
    all_metrics=Counter()
    for rep in range(64):
        q,m=3,4
        gates=[tuple((rng.randrange(1<<(q+i)),rng.randrange(2)) for _ in range(2)) for i in range(m)]
        out=(rng.randrange(1<<(q+m)),rng.randrange(2))
        expected=brute(q,gates,out)
        for defer in (False,True):
            count,metrics=reverse_count(q,gates,out,defer)
            assert count==expected
            all_metrics.update(metrics)
    print("128 complete-circuit exact count comparisons:",dict(all_metrics))


if __name__ == "__main__":
    main()

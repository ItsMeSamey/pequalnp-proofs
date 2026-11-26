#!/usr/bin/env python3
"""Compare the seven-survivor template formula to direct enumeration of R."""
from random import Random


def linear_map(columns):
    values = [0]
    for col in columns:
        values += [x ^ col for x in values]
    return values


def coordinates(x, order):
    return sum(((x >> pos) & 1) << i for i, pos in enumerate(order))


def check_case(n, G, P, T, survivors, contracted):
    masks = [(1 << n) - 1, sum(1 << i for i in survivors), sum(1 << i for i in contracted)]
    full, surv, contract = masks
    deleted = full ^ (surv | contract)
    # First construct the full reference, then shorten deleted positions and read survivors.
    full_reference = {gx ^ tc for x, gx in enumerate(linear_map(G))
                      if all((p & x).bit_count() % 2 == 0 for p in P) for tc in linear_map(T)}
    exact = {coordinates(y, survivors) for y in full_reference if not y & deleted}

    # Reduce G_J while carrying a preimage of each pivot; zero remainders yield a kernel basis.
    pivot = {}
    def reduce(w):
        preimage = 0
        for bit in sorted(pivot, reverse=True):
            if w >> bit & 1:
                col, pre = pivot[bit]
                w ^= col
                preimage ^= pre
        return w, preimage
    kernel = []
    for i, col in enumerate(G):
        rem, pre = reduce(col & ~contract)
        pre ^= 1 << i
        if rem:
            pivot[rem.bit_length()-1] = (rem, pre)
        else:
            kernel.append(pre)
    mu_p = [h for h in linear_map(P) if all((h & k).bit_count() % 2 == 0 for k in kernel)]
    t_j = linear_map([t & ~contract for t in T])
    for z in range(128):
        target = sum(((z >> i) & 1) << v for i,v in enumerate(survivors))
        allowed = False
        for tc in t_j:
            rem, pre = reduce(target ^ tc)
            if rem == 0 and all((h & pre).bit_count() % 2 == 0 for h in mu_p):
                allowed = True
                break
        assert allowed == (z in exact), (z,n,G,P,T,survivors,contracted)


def main():
    rng = Random(267367)
    cases = 0
    for i in range(180):
        n = rng.randrange(7, 14)
        d = rng.randrange(min(n, 7) + 1)
        # Systematic G with randomized surplus and physical coordinate order is injective.
        coords = rng.sample(range(n), n)
        G = [sum(1 << v for j,v in enumerate(coords)
                 if (j == k or (j >= d and rng.getrandbits(1)))) for k in range(d)]
        P = [rng.randrange(1 << d) for _ in range(rng.randrange(4))]
        T = [rng.randrange(1 << n) for _ in range(rng.randrange(4))]
        if i % 3 == 0:
            P.extend([0, P[0] if P else 0])
            T.extend([0, T[0] if T else 0])
        if i % 4 == 0 and G:
            T.append(G[0])
        order = rng.sample(range(n), n)
        check_case(n,G,P,T,order[:7],order[7:7+rng.randrange(n-6)])
        cases += 1
    print(f'passed {cases} templates and {128*cases} survivor-word tests')


if __name__ == '__main__':
    main()

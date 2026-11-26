from math import prod
from random import Random

def subspaces(h):
    spaces = [frozenset([0])]
    seen = set(spaces)
    for U in spaces:
        for x in range(1 << h):
            V = U | {x ^ v for v in U}
            if V not in seen:
                seen.add(V)
                spaces.append(V)
    return spaces

rng = Random(71)
for h in range(5):
    all_spaces = subspaces(h)
    coefficients = {R:-prod(1-2**j for j in range(1,h-len(R).bit_length()+1))
                    for R in all_spaces if len(R)<1<<h}
    for S in all_spaces:
        for y in range(1<<h):
            score = 1+sum(a for R,a in coefficients.items() if S<=R and y not in R)
            assert score == int(y in S)
    for _ in range(60):
        samples = [(rng.choice(all_spaces), rng.randrange(1<<h)) for d in range(32)]
        total = len(samples)+sum(a*sum(S<=R and y not in R for S,y in samples)
                                 for R,a in coefficients.items())
        assert total==sum(y in S for S,y in samples)
print('All subspace identities through dimension four and 300 collections passed')

from random import Random
from solve import indicator, witness_mod

rng = Random(37411)
checks = 0
for p, moduli in [(3,(3,)), (3,(3,3)), (3,(9,)), (5,(5,)), (7,(7,))]:
    for _ in range(75):
        k = rng.randrange(1,7)
        forms = [(rng.randrange(1 << k), rng.randrange(2),
                  tuple(rng.randrange(-q, q) for q in moduli)) for _ in range(rng.randrange(9))]
        target = tuple(rng.randrange(q) for q in moduli)
        spec = indicator(forms, p, moduli, target)
        hits = set()
        for y in range(1 << k):
            value = tuple(sum(ws[j] for a,b,ws in forms if (b+(a&y).bit_count())%2) % q
                          for j,q in enumerate(moduli))
            result = sum(v*(-1)**((a&y).bit_count()%2) for a,v in spec.items()) % p
            assert result == int(value == target)
            if result:
                hits.add(y)
        w = witness_mod(spec, p)
        assert w in hits if hits else w is None
        checks += 1
print(checks, "Walsh spectra and witnesses checked")

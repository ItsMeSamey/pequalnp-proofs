"""Exhaust one-edit recovery on all normalized clause lists on two variables."""
from itertools import product

words = list(product((-1,0,1), repeat=2))
ALL = 1<<len(words)


def image(mask,signed):
    out = 0
    for i,(a,b) in enumerate(words):
        if mask>>i&1:
            sign = -1 if signed else 1
            out |= 1<<words.index((b*sign,a*sign))
    return out


if __name__=='__main__':
    cases = ident = 0
    for template in range(ALL):
        actual = [(template^image(template,s)).bit_count() for s in (0,1)]
        for observed in [template]+[template^(1<<i) for i in range(len(words))]:
            measured = [(observed^image(observed,s)).bit_count() for s in (0,1)]
            assert all(abs(a-b)<=2 for a,b in zip(actual,measured))
            cases += 1
            if any(0<a<=4 for a in actual):
                continue
            assert [a==0 for a in actual]==[b<=2 for b in measured]
            generators = [s for s,b in enumerate(measured) if b<=2]
            orbits = set()
            for i in range(len(words)):
                orbit=1<<i
                while True:
                    current = orbit
                    for s in generators:
                        orbit |= image(orbit,s)
                    if orbit==current:
                        break
                orbits.add(orbit)
            for orb in orbits:
                if orb.bit_count()>2:
                    assert bool(template&orb)==(2*(observed&orb).bit_count()>orb.bit_count())
            ident += 1
    print(cases,'edit/template cases;',ident,'swap-gap cases')

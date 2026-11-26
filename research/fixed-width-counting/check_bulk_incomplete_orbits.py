"""Explicit orbit enumeration tests for capped violation products and selectors."""
from itertools import product, combinations
from math import comb, prod
from random import Random


def local(size,p,q,unbalanced):
    return [w for w in product((-1,0,1),repeat=size) if
            (sum(v!=0 for v in w)==p+q and (p+q<size or w.count(-1)%2==q%2)
             if unbalanced else w.count(1)==p and w.count(-1)==q)]


def local_count(size,p,q,unbalanced,weight):
    if unbalanced:
        return comb(size,p+q) if p+q<size else int(weight%2==q%2)
    if p>size-weight or q>weight:
        return 0
    return comb(size-weight,p)*comb(weight,q)


def violated(clause,x):
    return all(c==0 or (c<0)==bool(x>>i&1) for i,c in enumerate(clause))


def orbit_check(parts, rng, assignments):
    members = [sum(chunks,()) for chunks in product(*(local(*part) for part in parts))]
    holes = rng.sample(members,rng.randint(1,min(5,len(members)//2)))
    retained = set(members)-set(holes)
    cap = len(holes)+1
    revived = 0
    answers = []
    for x in assignments:
        current = 1
        offset = 0
        was_capped = False
        for size,p,q,unbalanced in parts:
            weight = ((x>>offset)&((1<<size)-1)).bit_count()
            factor = local_count(size,p,q,unbalanced,weight)
            current = min(cap,current*min(cap,factor))
            was_capped |= current==cap
            offset += size
        revived += was_capped and current==0
        target = sum(violated(c,x) for c in members)
        assert current==min(cap,target)
        valid = [violated(c,x) for c in holes]
        extensions = sum(all(valid[i] for i in s) for s in combinations(range(len(holes)),current))
        truth = not any(violated(c,x) for c in retained)
        assert extensions==truth
        answers.append((extensions,truth))
    return revived,answers


def check_signed_wide():
    # Bounded-arities encode both XOR and selector-to-falsity implications;
    # direct truth-table oracle below cross-checks the entire wide OR relation.
    for a in product((0,1),repeat=4):
        for output in (0,1):
            forward = all(not x or output for x in a)
            wide = not output or any(a)
            even = odd = 0
            for switch in (0,1):
                if forward and (not switch or not wide):
                    even += switch==0
                    odd += switch==1
            assert even-odd == (output==int(any(a)))


if __name__=='__main__':
    rng = Random(431)
    assignments = list(range(1<<7))
    cases = revived = 0
    for _ in range(120):
        # Nontrivial balanced or partial unbalanced first factor, allowing
        # saturation before later balanced or full unbalanced predicates vanish.
        parts1 = [(4,1,0,rng.choice((False,True))),
                  rng.choice([(3,3,0,False),(3,1,2,True),(3,0,0,False)])]
        parts2 = [(4,1,1,False),(3,0,1,True)]
        n1,v1 = orbit_check(parts1,rng,assignments)
        n2,v2 = orbit_check(parts2,rng,assignments)
        revived += n1+n2
        assert sum(a[0]*b[0] for x,(a,b) in enumerate(zip(v1,v2)) if x%3) == sum(
            a[1] and b[1] for x,(a,b) in enumerate(zip(v1,v2)) if x%3)
        cases += len(assignments)*2
    assert revived
    check_signed_wide()
    print(cases,'orbit-assignment tests;',revived,'cap-to-zero cases')

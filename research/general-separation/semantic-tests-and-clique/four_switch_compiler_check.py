"""Compare directed tours before and after the tied 4-switch compiler."""
from collections import Counter
from itertools import product
from random import Random


def single(p):
    seen = set()
    i = 0
    while i not in seen:
        seen.add(i)
        i = p[i]
    return i == 0 and len(seen) == len(p)


def original(sigma, groups):
    found = Counter()
    for bits in product((0, 1), repeat=len(groups)):
        p = list(sigma)
        for b, cycle in zip(bits, groups):
            if b:
                for i,j in zip(cycle,cycle[1:]+cycle[:1]):
                    p[i] = sigma[j]
        if single(p):
            found[bits] += 1
    return found


def compile_instance(sigma, groups, repeat):
    tracks = [[] for _ in sigma]
    bundles = []
    count = 0
    for cycle in groups:
        bundle = []
        for b in cycle[1:]:
            for _ in range(repeat):
                tracks[cycle[0]].append((count,0))
                tracks[b].append((count,1))
                bundle.append(count)
                count += 1
        bundles.append(bundle)
    # Isolated forced circuits must be handled before suppressing unary wires.
    remaining = set(range(len(sigma)))
    silent = 0
    while remaining:
        i = next(iter(remaining))
        touched = False
        while i in remaining:
            remaining.remove(i)
            touched |= bool(tracks[i])
            i = sigma[i]
        silent += not touched
    if silent:
        return None, bool(not count and silent == 1)

    feedback = {}
    for bundle in bundles:
        for i,j in zip(bundle,bundle[1:]+bundle[:1]):
            feedback[4*i+2] = 4*j
            feedback[4*j] = 4*i+1
    for i,visits in enumerate(tracks):
        if not visits:
            continue
        j = sigma[i]
        while not tracks[j]:
            j = sigma[j]
        for (a,port),(b,dest) in zip(visits,visits[1:]+[tracks[j][0]]):
            feedback[4*a+(1,3)[port]] = 4*b+(2,3)[dest]
    size = 4*count
    base = [feedback[i] for i in range(size)]
    alternate = [base[4*(i//4)+(i+1)%4] for i in range(size)]
    assert sorted(base) == sorted(alternate) == list(range(size))
    assert all(a != b for a,b in zip(base,alternate))
    # Each row has two distinct choices, each column occurs in both permutations.
    rows = [set(pair) for pair in zip(base,alternate)]
    assert Counter(j for row in rows for j in row) == Counter({v:2 for v in range(size)})
    inv = {v:i for i,v in enumerate(base)}
    tau = [inv[v] for v in alternate]
    for i in range(size):
        j = i
        for t in range(1,5):
            j = tau[j]
            assert (i == j) == (t == 4)
    if repeat == 3:
        assert all(i not in row for i,row in enumerate(rows))
    return (base,alternate,bundles), None


def check(sigma,groups,repeat,stats):
    expected = original(sigma,groups)
    compiled,constant = compile_instance(sigma,groups,repeat)
    if compiled is None:
        assert expected == (Counter({():1}) if constant else Counter())
        stats['constant_cases'] += 1
        return
    base,alt,bundles = compiled
    actual = Counter()
    for mask in range(1 << (len(base)//4)):
        p = [b if mask & (1 << (i//4)) else a for i,(a,b) in enumerate(zip(base,alt))]
        stats['compiled_settings'] += 1
        if single(p):
            choices = []
            for bundle in bundles:
                values = {(mask>>i)&1 for i in bundle}
                assert len(values) == 1, (sigma,groups,repeat,mask)
                choices.append(values.pop())
            actual[tuple(choices)] += 1
    assert actual == expected, (sigma,groups,repeat,expected,actual)
    stats['nonconstant_compilations'] += 1
    stats['compiled_tours'] += sum(actual.values())
    stats['with_tours'] += bool(actual)


def main():
    for repeat in [1,3]:
        rng = Random(47721)
        stats = Counter()
        for shape,extra in [((2,),0),((3,),0),((4,),0),((5,),0),
                            ((2,2),1),((2,3),1),((3,3),0),((2,),2),((),3)]:
            groups, n = [], 0
            for size in shape:
                groups.append(tuple(range(n,n+size)))
                n += size
            n += extra
            for i in range(10):
                sigma = list(range(n))
                if i == 1:
                    sigma = sigma[1:]+sigma[:1]
                elif i > 1:
                    rng.shuffle(sigma)
                check(sigma,groups,repeat,stats)
        print('serial repeats',repeat,dict(sorted(stats.items())))


if __name__ == '__main__':
    main()

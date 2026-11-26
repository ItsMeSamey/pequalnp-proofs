from itertools import combinations
from random import Random

from affine_selector_kernel import find_selector, selector_slices, solve_selector


def eq(x, row):
    mask,bit = row
    return (mask & x).bit_count()%2 == bit


def main():
    rng = Random(2191)
    total = 0
    for n in range(4,9):
        for trial in range(12):
            normals = [1<<i for i in range(n)]
            for _ in range(4*n):
                i,j = rng.sample(range(n),2)
                normals[i] ^= normals[j]
            forms = [(v,rng.randrange(2)) for v in normals[:4]]
            if trial%3 == 0:
                forms.append((normals[0]^normals[1]^normals[2],rng.randrange(2)))
            gates = []
            for i,j in combinations(range(len(forms)),2):
                p,a = forms[i]
                q,b = forms[j]
                if trial%4 == 1 and (i,j)==(0,1):
                    a ^= 1
                gates.append(((p,a^1),(p^q,a^b)))
            if trial%4 == 2:
                gates += [((normals[0],a),(normals[1],b)) for a in (0,1) for b in (0,1)]
            seed = [(normals[-1],trial%2)] if trial%2 else []
            if trial == 11:
                seed.append((normals[-1],1^(trial%2)))
            found = find_selector(n,gates)
            if trial%4 == 0 and trial%3:
                assert len(found) >= 4
            if trial%4 == 1:
                assert not set(forms) <= set(found)
            words = list(selector_slices(n,found,seed))
            assert len(words) <= len(found)+1
            good = []
            for x in range(1<<n):
                admitted = all(eq(x,r) for r in seed) and all(
                    not all(eq(x,r) for r in g) for g in gates)
                matches = sum(all(eq(x,r) for r in word) for word in words)
                assert matches <= 1
                if admitted:
                    assert matches == 1
                    good.append(x)
            witness = solve_selector(n,gates,seed)
            assert witness in good if good else witness is None
            total += 1
    gates = [((1,a),(2,b)) for a in (0,1) for b in (0,1)]*3
    assert not find_selector(2,gates)
    print(f"{total} dense signed controls passed, including dependent normals, seeds and near misses")


if __name__ == "__main__":
    main()

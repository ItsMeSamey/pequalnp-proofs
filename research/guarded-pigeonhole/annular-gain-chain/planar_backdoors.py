"""Explicit XP backdoor search and rooted witness lifting for native permutations."""
from itertools import combinations, product
from native_solver import IncompatiblePortOrder, _black_bits, _faces, _route, solve_native


def smooth(sigma, pinned):
    m = len(sigma)//3
    if len(sigma)%3 or sorted(sigma)!=list(range(3*m)):
        raise ValueError("expected a socket permutation")
    if any(g not in range(m) or b not in (0,1) for g,b in pinned.items()):
        raise ValueError("invalid gate pin")
    gates = [g for g in range(m) if g not in pinned]
    index = {3*g+j:3*i+j for i,g in enumerate(gates) for j in range(3)}
    # A root reaches either a surviving input or an entirely fixed orbit.
    image = {p:q for p,q in index.items()}
    for p in range(3*m):
        if p in image:
            continue
        path = []
        seen = set()
        u = p
        while u not in image and u not in seen:
            path.append(u)
            seen.add(u)
            g,j = divmod(u,3)
            u = sigma[3*g+(j+pinned[g])%3]
        target = image[u] if u in image else -1-min(path[path.index(u):])
        for v in path:
            image[v] = target
    smaller = [image[sigma[3*g+j]] for g in gates for j in range(3)]
    if sorted(smaller)!=list(range(len(smaller))):
        raise AssertionError("smoothing did not produce a permutation")
    return smaller,gates,image


def planar(sigma, pinned):
    small,_,_ = smooth(sigma,pinned)
    try:
        _black_bits(small)
        return True
    except IncompatiblePortOrder:
        return False


def backdoor(sigma, k, strong=True):
    """Return the strong gate tuple, or the weak pin dict, or None."""
    m = len(sigma)//3
    for d in range(min(k,m)+1):
        for gates in combinations(range(m),d):
            for bits in product((0,1),repeat=d):
                pins = dict(zip(gates,bits))
                good = planar(sigma,pins)
                if strong and not good:
                    break
                if not strong and good:
                    return pins
            else:
                if strong:
                    return gates
    return None


def solve_strong(sigma,first,second,gates):
    for bits in product((0,1),repeat=len(gates)):
        pinned=dict(zip(gates,bits))
        small,remaining,image = smooth(sigma,pinned)
        a,b=image[first],image[second]
        # A supplied non-strong set can raise IncompatiblePortOrder.
        if a<0 or b<0:
            _black_bits(small)
            if a!=b:
                continue
            small_mask=0
        else:
            small_mask=solve_native(small,a,b)
            if small_mask is None:
                continue
        mask=sum(pinned[g]<<g for g in gates)
        mask+=sum(((small_mask>>j)&1)<<g for j,g in enumerate(remaining))
        labels=_faces(_route(sigma,[(mask>>g)&1 for g in range(len(sigma)//3)]))
        assert labels[first]==labels[second]
        return mask
    return None


if __name__=='__main__':
    from random import Random
    rng=Random(26017)
    tests=branches=0
    gap=None
    for m in range(1,6):
        for trial in range(12):
            sigma=rng.sample(range(3*m),3*m)
            all_labels=[_faces(_route(sigma,[(mask>>g)&1 for g in range(m)]))
                        for mask in range(1<<m)]
            strong=backdoor(sigma,m)
            weak=backdoor(sigma,m,False)
            assert weak is not None and strong is not None and len(weak)<=len(strong)
            if len(weak)<len(strong) and gap is None:
                gap=(sigma,weak,strong)
            for bits in product((0,1),repeat=len(strong)):
                small,remaining,image=smooth(sigma,dict(zip(strong,bits)))
                for submask in range(1<<len(remaining)):
                    small_labels=_faces(_route(small,[(submask>>i)&1 for i in range(len(remaining))]))
                    value=sum(b<<g for g,b in zip(strong,bits))
                    value+=sum(((submask>>i)&1)<<g for i,g in enumerate(remaining))
                    lifted=[small_labels[image[p]] if image[p]>=0 else image[p] for p in range(3*m)]
                    expected=all_labels[value]
                    assert all((lifted[i]==lifted[j])==(expected[i]==expected[j])
                               for i in range(3*m) for j in range(i))
                    branches+=1
            for _ in range(3):
                a,b=rng.choices(range(3*m),k=2)
                mask=solve_strong(sigma,a,b,strong)
                assert (mask is not None)==any(row[a]==row[b] for row in all_labels)
                tests+=1
    print(tests,"root queries and",branches,"full masks verified; weak/strong gap",gap)

    adaptive_example=[4,6,8,2,11,10,5,3,1,9,7,0]
    assert len(backdoor(adaptive_example,4))==3
    assert all(planar(adaptive_example,{0:first,(1 if first else 2):second})
               for first,second in product((0,1),repeat=2))
    print("adaptive depth two verified against strong minimum three")

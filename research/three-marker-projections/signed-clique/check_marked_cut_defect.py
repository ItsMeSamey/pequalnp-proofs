"""Independent finite check of marked translations, triangle guesses and contractions."""
from itertools import combinations
from random import Random
from component_nullity import bits, dependencies, trace
from thick_tag_solver import basis, combine


def partitions(n):
    states = [()]
    for _ in range(n):
        states = [p+(j,) for p in states for j in range(max(p, default=-1)+2)]
    return states


def run(n, defects, rng):
    edges = list(combinations(range(n),2))
    N = len(edges)
    cuts = [sum(1<<i for i,e in enumerate(edges) if v in e) for v in range(n-1)]
    D = cuts + defects
    k = len(defects)
    if len(basis(D)[1]) != len(D):
        return False
    triangles = []
    for tri in combinations(range(n),3):
        w = sum(1<<i for i,e in enumerate(edges) if set(e)<=set(tri))
        color = sum(((w & z).bit_count()%2)<<j for j,z in enumerate(defects))
        triangles.append((tri,w,color))
    _, which = basis([c for _,_,c in triangles])
    assert len(which)==k
    markers = [triangles[j][1] for j in which]
    # Add arbitrary cut-orthogonal row combinations to the marker, as long
    # as its diagonal pairing with D/C is restored by an invertible basis.
    for j in range(k):
        candidate = markers[j] ^ rng.choice(triangles)[1]
        rows = markers[:j]+[candidate]+markers[j+1:]
        sig = [sum(((row&z).bit_count()%2)<<l for l,z in enumerate(defects)) for row in rows]
        if len(basis(sig)[1])==k:
            markers[j]=candidate
    labels = [rng.randrange(4) | sum(((row>>i)&1)<<(2+j) for j,row in enumerate(markers))
              for i in range(N)]
    # Obtain physical Q by an independent parity-check construction.
    sig = [sum(((w>>i)&1)<<j for j,w in enumerate(D)) for i in range(N)]
    checks = dependencies(sig)
    private = [sum(((w>>i)&1)<<j for j,w in enumerate(checks)) for i in range(N)]
    # Exhaustive physical supports. Subset zeta transform propagates the gain
    # of each word to every support containing it.
    tables = [0]*(1<<N)
    for w in range(1<<N):
        if combine(private,w)==0:
            tables[w] |= 1<<combine(labels,w)
    for i in range(N):
        for s in range(1<<N):
            if s&(1<<i):
                tables[s] |= tables[s^(1<<i)]
    targets = [1,3,5,9,15]
    true = {t for t in targets if t in tables}
    charge = [0]*n
    for i,(u,v) in enumerate(edges):
        charge[u] ^= labels[i]
        charge[v] ^= labels[i]
    found = set()
    for guessed in combinations(triangles,k):
        if len(basis([c for _,_,c in guessed])[1]) != k:
            continue
        # Literal contraction with transitive merging of overlapping triangles.
        reps = list(range(n))
        for tri,_,_ in guessed:
            merged = {reps[u] for u in tri}
            reps = [min(merged) if r in merged else r for r in reps]
        nodes = sorted(set(reps))
        local = [nodes.index(r) for r in reps]
        contracted = [0]*len(nodes)
        for i,c in zip(local,charge):
            contracted[i] ^= c
        for p in partitions(len(nodes)):
            block_charges = [0]*(max(p)+1)
            for i,c in zip(p,contracted):
                block_charges[i] ^= c
            gains = {combine(block_charges,w) for w in range(1<<len(block_charges))}
            t = sum(1<<g for g in gains)
            s = sum(1<<i for i,(u,v) in enumerate(edges) if p[local[u]]!=p[local[v]])
            assert tables[s]==t and trace(private,labels,s)==gains
            found.add(t)
    assert found.intersection(targets)==true
    return True


if __name__ == "__main__":
    rng = Random(8543)
    c4 = sum(run(4,[z],rng) for z in range(64))
    c5 = sum(run(5,[rng.randrange(1024) for _ in range(k)],rng)
             for k in (1,2) for _ in range(12))
    assert c4==56 and c5>=20
    print("K4 arbitrary single defect:",c4,"K5 sampled one/two-defect hosts:",c5)

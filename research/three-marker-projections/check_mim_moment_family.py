"""Check physical membership, dimension and query answers against enumeration."""
from itertools import combinations, product
from random import Random
from mim_moment_family import partition_moment_family, polynomial_witness


def rank(colorings, degree):
    pivots = {}
    for x in colorings:
        row = {tuple((v,x[v]) for v in sites)
               for j in range(degree+1) for sites in combinations(range(len(x)), j)}
        while row and max(row) in pivots:
            row ^= pivots[max(row)]
        if row:
            pivots[max(row)] = row
    return len(pivots)


def check(seed):
    rng = Random(seed)
    n = rng.randrange(2,7)
    p = rng.randrange(1,min(3,n)+1)
    degree = rng.randrange(3)
    vertices = list(range(n))
    nodes = vertices.copy()
    rng.shuffle(nodes)
    while len(nodes)>1:
        i = rng.randrange(len(nodes)-1)
        nodes[i:i+2] = [(nodes[i],nodes[i+1])]
    layout = nodes[0]
    edges = [(u,v) for u,v in combinations(vertices,2) if rng.randrange(2)]
    edges += [(0,0)] + edges[:1]
    pins = {rng.randrange(n):rng.randrange(p)} if seed%4==0 else {}
    anchors = rng.sample(vertices,p) if seed%3 else None
    moduli = (2,3) if seed%2 else ()
    charges = [tuple(rng.randrange(m) for m in moduli) for _ in vertices]
    fam = partition_moment_family(n,edges,layout,p,degree,moduli=moduli,
                                  charges=charges,pins=pins,anchors=anchors)
    actual = {}
    for x in product(range(p),repeat=n):
        if any(x[v]!=i for v,i in pins.items()):continue
        if anchors and any(x[v]!=i for i,v in enumerate(anchors)):continue
        for c in range(p):
            part={v for v in vertices if x[v]==c}
            if not part:break
            reached={min(part)}
            while True:
                old=reached.copy()
                for a,b in edges:
                    if a in reached and b in part:reached.add(b)
                    if b in reached and a in part:reached.add(a)
                if old==reached:break
            if reached!=part:break
        else:
            key=tuple(tuple(sum(charges[v][j] for v in vertices if x[v]==c)%m
                            for j,m in enumerate(moduli)) for c in range(p))
            actual.setdefault(key,[]).append(x)
    assert set(fam)==set(actual)
    for key,src in actual.items():
        assert set(fam[key])<=set(src)
        assert len(fam[key])==rank(fam[key],degree)==rank(src,degree)
        terms=[tuple((rng.randrange(n),rng.randrange(p)) for _ in range(rng.randrange(degree+1)))
               for _ in range(4)]
        sat=lambda x:sum(all(x[v]==c for v,c in mon) for mon in terms)%2
        w=polynomial_witness(fam,key,terms)
        assert (w is not None)==any(map(sat,src))
        if w is not None:assert w in src and sat(w)
    return len(actual)


if __name__=='__main__':
    total=sum(check(i) for i in range(150))
    print('150 exhaustive comparisons,',total,'feasible score buckets, all physical ranks and queries agree')

if __name__=='__main__':
    size=1100
    layout=0
    for v in range(1,size):
        layout=(layout,v)
    family=partition_moment_family(size,((i,i+1) for i in range(size-1)),
                                   layout,1,0,anchors=(0,))
    assert family=={((),):[(0,)*size]}
    print('1100-site unbalanced layout passed')

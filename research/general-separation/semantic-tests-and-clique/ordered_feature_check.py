"""Finite tests of feasible-ideal Mobius counting on binary-clause/affine features."""
from random import Random
from paired_violation_counter import signed_count


def holds(x, domain):
    clauses, rows = domain
    return (all(any(bool(x & (1 << (abs(v)-1))) == (v>0) for v in c) for c in clauses)
            and all((x & mask).bit_count()%2 == bit for mask,bit in rows))


def outer(y, k, gates):
    bits = [y>>i&1 for i in range(k)]
    for table,a,b in gates:
        bits.append(table>>(2*bits[a]+bits[b]) & 1)
    return bits[-1]


def check(q, features, common, phase, implications, gates):
    k = len(features)
    patterns = {}
    direct = 0
    for x in range(1<<q):
        if holds(x,common):
            y = sum(holds(x,feat)<<i for i,feat in enumerate(features))
            sign = (-1)**(sum(x&t==t for t in phase)%2)
            direct += sign*outer(y,k,gates)
            patterns[y] = patterns.get(y,0)+1
    requires = [1<<i for i in range(k)]
    for i,j in implications:
        assert all(not (y>>i&1) or y>>j&1 for y in patterns)
        requires[i] |= 1<<j
    for h in range(k):
        for i in range(k):
            if requires[i]>>h&1:
                requires[i] |= requires[h]
    # Equal reflexive predecessor closures characterize an implication SCC;
    # proper inclusion in predecessor closures orders all strict prerequisites.
    closures = sorted(set(requires),key=lambda w:(w.bit_count(),w))
    classes = [[j for j in range(k) if requires[j]==cl] for cl in closures]
    pred = [sum(1<<j for j,group in enumerate(classes) if j!=i and cl>>group[0]&1)
            for i,cl in enumerate(closures)]
    hist = {}
    tested = set()
    def visit(I, start, clauses, rows):
        assert I not in tested
        tested.add(I)
        size = signed_count(q,clauses,rows)
        if not size:
            return
        assert all((I&p)==p for j,p in enumerate(pred) if I>>j&1)
        z = signed_count(q,clauses,rows,phase)
        expanded = sum(1<<j for i,grp in enumerate(classes) if I>>i&1 for j in grp)
        assert size == sum(freq for y,freq in patterns.items() if y&expanded==expanded)
        hist[I] = (outer(expanded,k,gates),z,expanded in patterns)
        for i in range(start,len(classes)):
            if pred[i]&I == pred[i]:
                group = classes[i]
                visit(I|1<<i,i+1,clauses+[c for j in group for c in features[j][0]],
                      rows+[e for j in group for e in features[j][1]])
    visit(0,0,*common)
    weights = {i:item[0] for i,item in hist.items()}
    for j in reversed(range(len(classes))):
        for I in weights:
            donor = I^(1<<j)
            if I>>j&1 and donor in weights:
                weights[I] -= weights[donor]
    for I,(h,z,_) in hist.items():
        assert sum(w for J,w in weights.items() if I&J==J)==h
    assert sum(w*hist[I][1] for I,w in weights.items())==direct
    return len(hist), len(tested)-len(hist), sum(z==0 for _,z,_ in hist.values()),sum(not seen for _,_,seen in hist.values())


if __name__=='__main__':
    empty=([],[])
    # A and its copy are tied; C=A OR B is a supplied lower feature for A,B.
    # A and not-A cannot coexist, C and not-A can. The empty pattern is unrealized.
    feats=[([(1,)],[]),([] ,[(1,1)]),([(2,)],[]),([(1,2)],[]),([(-1,)],[])]
    edges=[(0,1),(1,0),(1,0),(0,3),(2,3)]
    gates=[(6,0,2),(11,1,4),(9,5,6),(7,7,3)]
    status=check(3,feats,empty,[1],edges,gates)
    assert all(status[i]>0 for i in range(4))
    # A canceled parent has nonzero signed child.
    assert check(1,[([(1,)],[])],empty,[1],[],[])==(2,0,1,0)
    assert check(2,feats,([()],[]),[3],edges,gates)==(0,1,0,0)
    rng=Random(9308)
    for _ in range(100):
        q,k=4,5
        feats=[]
        for j in range(k):
            lits=tuple(rng.choice((-1,1))*rng.randint(1,q) for _ in range(rng.randint(1,2)))
            feats.append(([lits],[(rng.randrange(1<<q),rng.randrange(2))] if rng.randrange(3)==0 else []))
        common=([(-1,2)],[]) if rng.randrange(2) else empty
        raw=[x for x in range(1<<q) if holds(x,common)]
        edges=[(i,j) for i in range(k) for j in range(k) if i!=j and rng.randrange(2)
               and all(not holds(x,feats[i]) or holds(x,feats[j]) for x in raw)]
        gates=[(rng.randrange(16),rng.randrange(k+j),rng.randrange(k+j)) for j in range(8)]
        phase=[m for m in range(1<<q) if m.bit_count()<=2 and rng.randrange(3)==0]
        check(q,feats,common,phase,edges,gates)
    print('100 seeded arbitrary outer DAGs and three structured cases passed; structured metrics',status)

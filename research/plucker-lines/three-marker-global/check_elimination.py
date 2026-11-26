"""Independent finite audit of weighted elimination across a binary overlap of rank <=2.

Vectors live in common ambient coordinates. Each ordinary labeled column is a
(vector,bit) occurrence; s,t,u lie on the retained side. The answer is the set
of primal label XOR dual moment d(u), subject to d(s)=1, d(t)=0 and a subset
of annihilated ordinary vectors summing to t. A fixed root label is just a shift.
"""
from collections import Counter
from itertools import product
from random import Random


def parity(x):
    return x.bit_count() & 1


def span(vectors):
    S={0}
    for v in vectors:
        S |= {x^v for x in S}
    return S


def words(columns):
    """Enumerate occurrence subsets, retaining sum, weight, and member list."""
    out=[(0,0,())]
    for v,w in columns:
        out.extend([(x^v,y^w,occ+(v,)) for x,y,occ in out])
    return out


def eligible_words(columns,d):
    """Direct enumeration in the eligible column list, independent of the summary."""
    out={(0,0)}
    for v,w in columns:
        if not parity(d&v):
            out |= {(x^v,y^w) for x,y in out}
    return out


def exact(dim, A, B, s,t,u):
    result=set()
    for d in range(1<<dim):
        if not parity(s&d) or parity(t&d):
            continue
        result.update(w^parity(d&u) for x,w in eligible_words(A+B,d) if x==t)
    return result


def audit(dim,A,B,s,t,u,counts):
    SA=span([v for v,_ in A]+[s,t,u])
    SB=span(v for v,_ in B)
    H=SA&SB
    h=len(H).bit_length()-1
    assert h<=2
    hbase=[]
    for v in sorted(H):
        if v not in span(hbase):
            hbase.append(v)
    def trace(d):
        return sum(parity(d&v)<<i for i,v in enumerate(hbase))
    ds=range(1<<dim)
    truth=exact(dim,A,B,s,t,u)
    # Summaries built by independently iterating B subsets, then testing all covectors.
    table={(delta,w):set() for delta in range(1<<h) for w in H}
    for w,value,occ in words(B):
        if w in H:
            for d in ds:
                if all(not parity(d&v) for v in occ):
                    table[trace(d),w].add(value)
    # Explicit quotient SA/H. Canonical coset leaders preserve XOR coset classes.
    def coset(x):
        return min(x^j for j in H)
    qA=[coset(v) for v,_ in A]
    def outside(mask_tests,want,cols):
        for d in ds:
            if not parity(mask_tests[0]&d) or any(parity(d&v) for v in mask_tests[1:]):
                continue
            if want in span(v for v in cols if not parity(v&d)):
                return True
        return False
    reaches_zero=outside([coset(s)],coset(t),qA)
    # Independent joint enumeration of exact outside trace/target states.
    direct=set()
    for a_sum,_,occ in words(A):
        w=t^a_sum
        if w in H:
            for d in ds:
                if parity(s&d) and not parity(t&d) and all(not parity(d&v) for v in occ):
                    direct.add((trace(d),w))
    assert reaches_zero==any(delta==0 for delta,_ in direct)
    if reaches_zero and len(table[0,0])==2:
        assert truth=={0,1}
        counts[h,"zero-flex"]+=1
        return
    # Every nonzero trace has a kernel with at most one nonzero vector.
    points=[]
    for delta in range(1,1<<h):
        representative=next(d for d in ds if trace(d)==delta)
        kernel=[w for w in H if not parity(representative&w)]
        p=next((w for w in kernel if w),0)
        for w in kernel:
            cell=table[delta,w]
            reached=outside([s,p],t^w,[v for v,_ in A])
            assert reached==((delta,w) in direct or (0,w) in direct)
            if len(cell)==2 and reached:
                assert truth=={0,1}
                counts[h,"mixed-flex"]+=1
                return
        if p and table[delta,p]:
            points.append((p,table[delta,p]))
    if h==1:
        p=next(w for w in H if w)
        points=[(p,table[0,p])]
    assert span(p for p,_ in points)==H
    for signs in product(*(available for _,available in points)):
        triangle=[(p,sign) for (p,_),sign in zip(points,signs)]
        actual=exact(dim,A,triangle,s,t,u)
        assert actual==truth,(A,B,s,t,u,H,table,triangle,truth,actual)
    counts[h,"baseline"]+=1


if __name__=='__main__':
    rng=Random(77816)
    counts=Counter()
    for h in range(3):
        for i in range(380):
            a,b=rng.randrange(3),rng.randrange(3)
            dim=h+a+b
            # Span generators ensure H really has the specified rank.
            Va=[1<<j for j in range(h+a)]
            Vb=[1<<j for j in range(h)]+[1<<j for j in range(h+a,dim)]
            # Apply random invertible shear/permutation coordinates. This also
            # tests quotient calculations when H is not a coordinate subspace.
            basis=[1<<j for j in range(dim)]
            for _ in range(4*dim):
                if dim>=2:
                    j,k=rng.sample(range(dim),2);basis[j]^=basis[k]
            def mv(x):
                z=0
                for j,q in enumerate(basis):
                    if x>>j&1:z^=q
                return z
            def pick(vs):
                return rng.choice(sorted(span(vs)))
            # Occasionally suppress explicit overlap generators in one of the
            # ordinary lists, so protected s,t,u may be needed on side A.
            colsA=[mv(v) for v in Va if rng.randrange(4)]
            colsA += [mv(pick(Va)) for _ in range(rng.randrange(4))]
            # Mix basis of B so mixed points of H need not be actual columns.
            bgen=Vb.copy()
            for _ in range(3*len(bgen)):
                if len(bgen)>=2:
                    j,k=rng.sample(range(len(bgen)),2);bgen[j]^=bgen[k]
            colsB=[mv(v) for v in bgen]+[mv(pick(Vb)) for _ in range(rng.randrange(4))]
            ga,gb=rng.getrandbits(dim),rng.getrandbits(dim)
            A=[(v,parity(v&ga) if i%3==0 else rng.randrange(2)) for v in colsA]
            B=[(v,parity(v&gb) if i%3==0 else rng.randrange(2)) for v in colsB]
            s,t,u=(mv(pick(Va)) for _ in range(3))
            audit(dim,A,B,s,t,u,counts)
    print("Passed",sum(counts.values()),"exact elimination audits:",dict(sorted(counts.items())))

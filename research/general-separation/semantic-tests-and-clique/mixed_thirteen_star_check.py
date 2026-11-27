"""Bounded structural checks for the mixed thirteen-state star, h=0, T={1,2,3}."""
from itertools import combinations,product
from random import Random
from collections import Counter
from general_fourteen_check import bits,fixed,verify


def active_profile(table):
    return tuple(frozenset(d&s for d in range(4) if table>>(4*s+d)&1) for s in range(4))


def classify(table):
    opts=active_profile(table)
    # Structural premise for physically possible >=13 tables at a forced singleton.
    if any(len(opts[s])==1 for s in (1,2)) and len(opts[3])==3:
        return "violates physical affine-fiber premise"
    for s in (1,2,3):
        for bit in (1,2):
            if s&bit and len({v&bit for v in opts[s]})==1:
                if len(opts[3])==1:
                    return "double"
                return "directed"
    return "ordinary"


def classify_all():
    counts=Counter()
    for num in range(4):
        for holes in combinations(range(16),num):
            t=65535 ^ sum(1<<j for j in holes)
            kind=classify(t)
            counts[kind]+=1
            p=active_profile(t)
            if kind=="double":
                assert all(len(p[s])==(1<<s.bit_count()) for s in (0,1,2))
            if kind=="ordinary":
                assert all(len(p[s])==2 for s in (1,2))
                assert all({d&b for d in p[3]}=={0,b} for b in (1,2))
            if kind=="directed":
                matches=[]
                for tail,trigger,forced in product((1,2),(0,1),(0,1)):
                    head=tail^3
                    pred=tuple(frozenset(d for d in range(4) if not d&~s and
                               (not s&tail or bool(s&head)!=trigger or bool(d&tail)==forced))
                               for s in range(4))
                    if pred==p:
                        matches.append((tail,trigger,forced))
                assert matches
    return dict(counts)


def raw(rows,c,edges,w,permanent):
    # A free site has an extra unconstrained adjustment bit, tested by direct
    # XOR convolution independently of the fixed-occupancy construction.
    states={0}
    for i,j,t in edges:
        s=((w>>i)&1)|(((w>>j)&1)<<1)
        local={(((d&1)<<i)|((d>>1)<<j))&w&~permanent for d in range(4) if t>>(4*s+d)&1}
        states={a^b for a in states for b in local}
    demand=(c^sum(((r&w).bit_count()%2)<<i for i,r in enumerate(rows))) & w & ~permanent
    return demand in states


def check():
    rng=Random(632514)
    tallies=Counter()
    for trial in range(160):
        n=8
        # Two-site ordinary component C={0,4}; neither is a directed head.
        edges=[(0,4,65535^(1<<13)^(1<<14))]
        tail_base=0
        planted=trial%4==0
        for i in (1,2,3):
            for _ in range(1+(trial%5==0)):
                d=0 if planted else rng.randrange(4)
                edges.append((i,0,4095|(1<<(12+d))))
                tail_base^=(d&1)<<i
        trigger=rng.randrange(2)
        f=rng.randrange(2)
        holes=[4*(1+2*trigger)+(1^f)+2*h for h in (0,1)]
        edges.append((6,5,65535 ^ sum(1<<v for v in holes)))
        edges.append((7,5,4095|(1<<(12+rng.randrange(4)))))
        if trial%2:
            edges.append((4,7,4095|(1<<(12+rng.randrange(4)))))
        permanent=(1<<5) if trial%3==0 else 0
        rows=[0]*n
        def edge(i,j):
            rows[i]^=1<<j
            rows[j]^=1<<i
        if planted:
            edge(1,2)
            edge(2,3)
            edge(3,4)
            beta=2
            c=2
        else:
            for i,j in combinations(range(n),2):
                if rng.randrange(2):
                    edge(i,j)
            c=rng.randrange(1<<n)
            beta=rng.randrange(1,8)<<1
        possible=set()
        actual=set()
        for w in range(1,1<<n,2):
            if not (beta&w).bit_count()%2:
                continue
            d=c^tail_base^sum(((r&w).bit_count()%2)<<i for i,r in enumerate(rows))
            if not w&14&d:
                possible.add(w)
            if raw(rows,c,edges,w,permanent):
                actual.add(w)
        assert actual<=possible
        candidates={w for w in actual if w&30!=30}
        if not candidates:
            assert all(w&30==30 for w in possible)
            # With h,T fixed, the 4 remaining bits have affine feasible and
            # affine failed sets, so a nonempty proper projection is a hyperplane.
            projection={w>>4 for w in possible}
            assert len(projection) in (0,8,16)
            if projection:
                anchor=min(projection)
                assert all((x^y^anchor) in projection for x,y in product(projection,repeat=2))
            tallies["no vacancy / nonempty projection" if possible else "no vacancy / empty"]+=1
        else:
            tallies["has vacancy"]+=1
    print("raw structural counts",classify_all())
    print("star fibers",dict(tallies))


if __name__=="__main__":
    check()

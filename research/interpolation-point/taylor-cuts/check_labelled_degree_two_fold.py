"""Ground controls for folding, parallel variants, offsets and original lifts."""
from itertools import combinations, product
from random import Random
from labelled_degree_two_fold import fold, search, dense_search


def words(n,edges):
    def rec(remaining,selected):
        if not remaining:
            yield selected
            return
        v=min(remaining)
        for i,(a,b,_) in enumerate(edges):
            if v in (a,b) and {a,b}<=remaining:
                yield from rec(remaining-{a,b},selected+(i,))
    return list(rec(set(range(n)),()))


def total(edges,ids,b):
    return tuple(sum(edges[i][2][j] for i in ids)%3 for j in range(b))


def brute(n,edges,target):
    for ids in words(n,edges):
        if total(edges,ids,len(target))==target:
            return "SAT",ids
    return "UNSAT",None


rng=Random(23011)
ground=0
for _ in range(220):
    n=rng.randrange(9)
    pairs=list(combinations(range(n),2))
    b=rng.randrange(3)
    edges=[(*rng.choice(pairs),tuple(rng.randrange(3) for _ in range(b)))
           for _ in range(rng.randrange(14))] if pairs else []
    original={tuple(sorted(w)) for w in words(n,edges)}
    feasible={total(edges,w,b) for w in original}
    for target in product(range(3),repeat=b):
        status,ids=search(n,edges,target,brute)
        assert (status=="SAT")==(target in feasible)
        assert ids is None or tuple(sorted(ids)) in original and total(edges,ids,b)==target
        ground+=1

# A 160-cycle has exactly two simple perfect matchings.
n=160
edges=[(i,(i+1)%n,(int(i==0),int(i==1))) for i in range(n)]
for target in product(range(3),repeat=2):
    f=fold(n,edges,target)
    assert f.n==0 and f.folded>60
    status,ids=search(n,edges,target,lambda *args: (_ for _ in ()).throw(AssertionError("unexpected core")))
    assert (status=="SAT")==(target in {(1,0),(0,1)})

# For odd subdivisions every core matching determines the entire path parity.
for size in (4,6,8):
    base=list(combinations(range(size),2))
    paths=[]
    edges=[]
    n=size
    for u,v in base:
        # A deterministic mix of 3- and 5-edge subdivisions.
        length=rng.choice([3,5])
        chain=[u,*range(n,n+length-1),v]
        n+=length-1
        path=[]
        for a,b in zip(chain,chain[1:]):
            path.append(len(edges))
            edges.append((a,b,tuple(rng.randrange(3) for _ in range(2))))
        paths.append(path)
    source={tuple(sorted(k for i,p in enumerate(paths) for k in p[(0 if i in match else 1)::2]))
            for match in words(size,[(a,b,()) for a,b in base])}
    feasible={total(edges,w,2) for w in source}
    for target in product(range(3),repeat=2):
        def dense(core,es,t):
            assert core==size and {tuple(sorted(e[:2])) for e in es}==set(combinations(range(size),2))
            return brute(core,es,t)
        status,ids=search(n,edges,target,dense)
        assert (status=="SAT")==(target in feasible)
        assert ids is None or tuple(sorted(ids)) in source and total(edges,ids,2)==target
        status,ids=dense_search(n,edges,target)
        assert (status=="SAT")==(target in feasible)
        assert ids is None or tuple(sorted(ids)) in source and total(edges,ids,2)==target

# Both the feasible external side and the interior parallel-edge label matter.
edges=[(0,1,(0,)),(0,1,(2,)),(1,2,(0,)),(2,3,(1,)),(0,3,(0,))]
assert search(4,edges,(0,),brute)[0]=="SAT"
# Unknown residual calls cannot support a negative conclusion.
es=[(a,b,(0,)) for a,b in combinations(range(4),2)]+[(4,5,(0,)),(4,5,(1,))]
assert search(6,es,(0,),lambda *_:("UNKNOWN",None))[0]=="UNKNOWN"
print(ground,"multigraph target decisions; 160-cycle, odd subdivisions of K4/K6/K8, and residual-status controls passed")

"""Compare branch and path tables with direct control and generator enumeration."""
from random import Random
from closure_generator_tree import solve, solve_prepared
from two_sat_generator_interaction import prepare

rng = Random(14891)
for _ in range(200):
    n = rng.randrange(1,8)
    clauses = [tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randint(1,2)))
               for _ in range(rng.randrange(12))]
    rows = [(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(6))]
    data = prepare(n,clauses,rows)
    bags = [range(len(data['closures']))] if data else [[]]
    x,choice,s = solve(n,clauses,rows,bags,[])
    feasible = [v for v in range(1<<n)
                if all(any(bool(v>>(abs(l)-1)&1) == (l>0) for l in c) for c in clauses)
                and all((v&m).bit_count()%2 == b for m,b in rows)]
    assert x in feasible if feasible else x is None
    if s:
        assert s['peak_per_word'] <= 1 << s['max_cut_rank']

for _ in range(250):
    # Build a random bag tree, connected generator subtrees, and legal local scopes.
    b = rng.randrange(1,8)
    parents = [rng.randrange(i) for i in range(1,b)]
    edges = [(p,i) for i,p in enumerate(parents,1)]
    bags = [set() for _ in range(b)]
    g = rng.randrange(1,8)
    for j in range(g):
        root = rng.randrange(b)
        bags[root].add(j)
        for i,p in enumerate(parents,1):
            if j in bags[p] and rng.randrange(2):
                bags[i].add(j)
    scopes = [set(rng.sample(sorted(row), rng.randint(1,len(row))))
              for row in bags if row for _ in range(rng.randint(1,3))]
    closures = tuple(sum(1<<i for i,scope in enumerate(scopes) if j in scope) for j in range(g))
    conflicts = [rng.sample(sorted(row),2) for row in bags if len(row)>=2 and rng.randrange(2)]
    labels = [rng.randrange(8) for _ in scopes]
    base = rng.randrange(1<<len(scopes))
    t = rng.randrange(8)
    data = dict(baseline=base,closures=closures,labels=labels,conflicts=conflicts,target=t)
    def realize(choice):
        toggle = 0
        for j,c in enumerate(closures):
            if choice >> j & 1:
                toggle |= c
        label = 0
        for i,w in enumerate(labels):
            if toggle >> i & 1:
                label ^= w
        if any((choice>>a)&(choice>>b)&1 for a,b in conflicts) or label != t:
            return None
        return base ^ toggle
    x, choice, stats = solve_prepared(data,bags,edges)
    feasible = [z for v in range(1<<g) if (z:=realize(v)) is not None]
    assert (x in feasible and realize(choice)==x) if feasible else choice is None and x is None
    assert stats['peak_per_word'] <= 1 << stats['max_cut_rank']

# Unbounded syndrome rank and graph degree, bag size two, zero syndrome width.
m = 40
clauses = [(-1,-i) for i in range(2,m+2)]
rows = [(1<<i, i%3==1) for i in range(1,m+1)]
bags = [[0,i] for i in range(1,m+1)]
x,choice,stats = solve(m+1,clauses,rows,bags,[(j,j+1) for j in range(m-1)])
assert x is not None and stats['max_cut_rank']==0 and stats['peak_per_word']==1

# Two always co-toggled columns cancel even though all generators share them.
y,z = m+1,m+2
clauses = [(-i,y) for i in range(1,m+1)]+[(-y,z),(-z,y)]
rows = [(1<<i | (((1<<(y-1))|(1<<(z-1))) if i==0 else 0),i%3==1) for i in range(m)]
data = prepare(m+2,clauses,rows)
g = len(data['closures'])
x,choice,stats = solve(m+2,clauses,rows,[[i] for i in range(g)],[(i,i+1) for i in range(g-1)])
assert x is not None and stats['bundles']==m and stats['max_cut_rank']==0

# High node degree requires accounting for the temporary join cuts as well.
m=5
data=dict(closures=[1<<j for j in range(2*m)],labels=[1<<j for j in range(m)]*2,
          conflicts=[],target=0,baseline=0)
x,choice,stats=solve_prepared(data,[[]]+[[j] for j in range(2*m)],[(0,j+1) for j in range(2*m)])
assert x is not None and stats['max_cut_rank']==m and stats['peak_per_word']==1<<m

def rejected(data,bags,edges):
    try:
        solve_prepared(data,bags,edges)
    except ValueError:
        return
    raise AssertionError("invalid decomposition accepted")

data = dict(closures=(1,2),labels=(1,2),conflicts=((0,1),),target=0,baseline=0)
rejected(data,[[0],[1]],[(0,1)])
rejected(data,[[0,1],[],[0]],[(0,1),(1,2)])
rejected(data,[[0,1],[],[]],[(0,1),(1,2),(0,2)])
rejected(data,[[0],[]],[(0,1)])
data = dict(closures=(3,5),labels=(1,0,0),conflicts=(),target=1,baseline=0)
rejected(data,[[0],[1]],[(0,1)])
print("200 source comparisons, 250 generator-tree comparisons, two rank-40 controls, virtual-cut and five rejection checks passed")

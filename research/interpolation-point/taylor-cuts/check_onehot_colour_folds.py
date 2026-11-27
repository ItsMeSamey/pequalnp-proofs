from itertools import combinations,product
from random import Random
from onehot_colour_folds import solve,colour

def encode(n,edges,rng):
    ids=list(range(1,3*n+1));rng.shuffle(ids)
    blocks=[tuple(i*rng.choice((-1,1)) for i in ids[j:j+3]) for j in range(0,len(ids),3)]
    cs=[(-a,-b) for row in blocks for a,b in combinations(row,2)]
    cs += [(-blocks[u][k],-blocks[v][k]) for u,v in edges for k in range(3)]
    rows=[(sum(1<<(abs(l)-1) for l in row),1^(sum(l<0 for l in row)%2)) for row in blocks]
    rng.shuffle(rows);rng.shuffle(cs)
    return cs,rows

def check(n,E,rng,expected=None):
    cs,rows=encode(n,E,rng);s,w,metrics=solve(3*n,cs,rows)
    if expected is None:
        expected=any(all(c[u]!=c[v] for u,v in E) for c in product(range(3),repeat=n))
    if s!='UNKNOWN':assert (s=='SAT')==expected
    if w is not None:assert all(any(bool(w>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs)
    return s,metrics

if __name__=='__main__':
    rng=Random(13123);seen=set();cases=0
    for n in range(6):
        all_edges=list(combinations(range(n),2))
        for mask in range(1<<len(all_edges)):
            E=[e for i,e in enumerate(all_edges) if mask>>i&1]
            s,m=check(n,E,rng);seen.update(m);cases+=1
    pet=sorted({tuple(sorted(e)) for i in range(5) for e in ((i,(i+1)%5),(i+5,(i+2)%5+5),(i,i+5))})
    s,m=check(10,pet,rng,True);assert s=='SAT' and m['subcubic_order']
    remap=lambda i:i if i in (0,1) else i+8
    joined=set(pet)|{(remap(i),remap(j)) for i,j in pet}
    s,m=check(18,joined,rng,True);assert s=='SAT' and m['clique_cut']
    wheel=[(i,(i+1)%5) for i in range(5)]+[(i,5) for i in range(5)]
    s,m=check(6,wheel,rng,False);assert s=='UNSAT' and m['odd_neighbourhood']
    clebsch=sorted({tuple(sorted((x,x^b))) for x in range(16) for b in (1,2,4,8,15)})
    cs,rs=encode(16,clebsch,rng);assert solve(48,cs,rs)[0]=='UNKNOWN'
    malformed,rs=encode(3,[(0,1),(1,2)],rng)
    assert solve(9,malformed+[(1,)],rs)[0]=='UNKNOWN'
    assert solve(9,malformed,rs,max_nodes=0)[0]=='UNKNOWN'
    for _ in range(300):
        n=8; E=[e for e in combinations(range(n),2) if rng.random()<.43]
        s,m=check(n,E,rng);seen.update(m)
    assert 'diamond' in seen and 'domination' in seen,seen
    print(cases,'labelled graphs on at most five vertices; 300 random 8-vertex cases; fixtures Petersen, two glued Petersen graphs, odd wheel, stalled Clebsch')
    # Ordinary local names on a nontrivially twisted 5-cycle cannot synchronize.
    n=5; row=[[3*v+i+1 for i in range(3)] for v in range(n)]
    cs=[(-a,-b) for triple in row for a,b in combinations(triple,2)]
    for v in range(n):
        for i in range(3):
            k=(i+1)%3 if v==n-1 else i
            cs.append((-row[v][i],-row[(v+1)%n][k]))
    rs=[(sum(1<<(i-1) for i in triple),1) for triple in row]
    status,w,m=solve(3*n,cs,rs)
    assert status=='SAT' and m['twisted_peels']==n
    print('nonsynchronized correspondence cycle fully peeled and replayed')

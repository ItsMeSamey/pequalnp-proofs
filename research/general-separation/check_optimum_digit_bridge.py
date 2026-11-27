"""Physical matching census, constructive named lift and direct edge-cover sums."""
from itertools import permutations
from math import prod
from read_two_min_cost import minimum_cost


def cube(n,edges,expected):
    clauses=[[i for i,(a,b) in enumerate(edges) if (a,b)[side]==v]
             for side in range(2) for v in range(n)]
    weighted=0
    for mask in range(1<<len(edges)):
        if all(any(mask>>i&1 for i in c) for c in clauses):
            j=mask.bit_count()
            weighted+=3**j*(-2)**(len(edges)-j)
    assert weighted%3**(n+1)==3**n*(expected%3)
    cost,bits=minimum_cost([{0:0,1:1} for _ in edges],
                           [[(i,(1,)) for i in c] for c in clauses])
    assert cost==sum(bits)==n and all(sum(bits[i] for i in c)==1 for c in clauses)


def split(matrix):
    n=len(matrix)
    edges=[]
    named=set()
    for i in range(n):
        for j in range(n):
            edges.extend([(i,n+j)]*(matrix[i][j]%3))
            if i==j:
                named.add(len(edges))
                edges.extend([(i,n+j)]*3)
    adj={}
    def link(v,w):
        assert w not in adj.setdefault(v,set())
        adj[v].add(w)
        adj.setdefault(w,set()).add(v)
        return frozenset((v,w))
    count=[0]*(2*n)
    lift=set()
    used={}
    for e,(i,j) in enumerate(edges):
        a,b=(i,2*count[i]),(j,2*count[j])
        pair=link(a,b)
        if e in named:
            lift.add(pair)
            used[i],used[j]=a[1],b[1]
        count[i]+=1
        count[j]+=1
    for v,d in enumerate(count):
        selected=used[v]
        for a in range(2*d-2):
            pair=link((v,a),(v,a+1))
            if (a<selected and a%2==0) or (a>selected and a%2==1):
                lift.add(pair)
    M=2*len(edges)-n
    assert len(adj)==2*M and len(lift)==M
    assert set().union(*lift)==set(adj) and max(map(len,adj.values()))<=3
    def physical(free):
        if not free:
            return 1
        v=min(free,key=lambda u:(len(adj[u]&free),u))
        return sum(physical(free-{v,w}) for w in adj[v]&free)
    got=physical(set(adj))
    def permanent(mat):
        return sum(prod(mat[i][j] for i,j in enumerate(p)) for p in permutations(range(n)))
    padded=[[sum(e==(i,n+j) for e in edges) for j in range(n)] for i in range(n)]
    assert got==permanent(padded) and got%3==permanent(matrix)%3


if __name__=='__main__':
    for n,m in [(1,1),(2,2),(3,6)]:
        cube(n,[(i,j) for i in range(n) for j in range(n)],m)
    for mat in ([[0]],[[-1]],[[0,2],[-1,1]],[[1,0],[0,-2]],[[0,1],[1,0]]):
        split(mat)
    print('Three original-cube digits, minimizing witnesses and five physical split lifts passed.')

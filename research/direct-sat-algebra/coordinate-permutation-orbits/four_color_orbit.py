"""Two-permutation construction with four positions per translation orbit."""
from itertools import combinations
from orbit_subcube import Orbit,apply_word

def build(n,edges):
    if type(n)!=int or n<1:raise ValueError('positive graph order required')
    edges=tuple(edges)
    if any(not (0<=u<n and 0<=v<n) for u,v in edges):raise ValueError('invalid index')
    if any(u==v for u,v in edges):raise ValueError('requires a simple graph')
    m=n+(n%2==0)
    coords=[(u,v,a) for u,v in combinations(range(m),2) for a in range(4)]
    ids={c:i for i,c in enumerate(coords)}
    R=[];F=[];start=0
    for i,(u,v,a) in enumerate(coords):
        x,y=sorted(((u+1)%m,(v+1)%m))
        R.append(ids[x,y,((a&1)<<1)|(a>>1)])
        F.append(ids[u,v,a^(u==0 or v==0)])
        if not a:start|=1<<i
    zero=0
    for u,v in edges:zero|=1<<ids[*sorted((u,v)),0]
    return Orbit(tuple(R),tuple(F),start,zero)

def decode(n,edges,word):
    edges=tuple(edges);instance=build(n,edges);v=apply_word(instance,word)
    if v&instance.zero:raise ValueError('not a proper coloring')
    colors=[0]
    for j in range(1,n):
        cell=(v>>(4*(j-1)))&15
        if cell.bit_count()!=1:raise ValueError('invalid orbit state')
        colors.append(cell.bit_length()-1)
    assert all(colors[u]!=colors[w] for u,w in edges)
    return colors

if __name__=='__main__':
    from orbit_subcube import move
    from itertools import product
    for n in (3,4,5):
        edges=list(combinations(range(n),2));I=build(n,[])
        assert sorted(I.rotation)==sorted(I.flip)==list(range(I.dimension))
        seen={I.start:''};queue=[I.start]
        for v in queue:
            for s,f in (('r',I.rotation),('f',I.flip)):
                b=move(f,v)
                if b not in seen:seen[b]=seen[v]+s;queue.append(b)
        assert len(seen)==4**(n+(n%2==0)-1)
        graphs=list(range(1<<len(edges))) if n<5 else [0,1023]+list(range(19,1024,29))
        for graph in graphs:
            e=[x for i,x in enumerate(edges) if graph>>i&1]
            t=build(n,e);hit=next((w for s,w in seen.items() if not s&t.zero),None)
            sat=any(all(c[u]!=c[v] for u,v in e) for c in product(range(4),repeat=n))
            assert (hit is not None)==sat
            if sat:decode(n,e,hit)
    print('three graph sizes; all orbit cardinalities, subcube decisions and color lifts agree')

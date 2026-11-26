"""Four-endpoint encoder positive control on PG(2,2), affine host t=2."""
from itertools import product

def incident(p, s):
    return (((p+1) & (s+1)).bit_count() % 2) == 0

def edge(label):
    x,y,m = ((label >> k) & 1 for k in (2,1,0))
    return (x,y), (m,y^(m&x))

edges = {edge(p): p for p in range(7)}
exceptions = {(p,s) for p in range(7) for s in range(p+1,7)
              if incident(p,s) and any(a==b for a,b in zip(edge(p),edge(s)))}
hist = {}
for r,c in product(range(7),repeat=2):
    ps = {edge(j)[0] for j in (r,c)}
    ls = {edge(j)[1] for j in (r,c)}
    k = len(ps)+len(ls)
    hist[k] = hist.get(k,0)+1
    answer = (r==c and incident(r,r)) or tuple(sorted((r,c))) in exceptions
    if k == 4:
        a,b=ps; x,y=ls
        matches=[(edges[a,u],edges[b,v]) for u,v in ((x,y),(y,x))
                 if (a,u) in edges and (b,v) in edges]
        assert len(matches)==1
        answer |= incident(*matches[0])
    assert answer==incident(r,c), (r,c)
print('49/49; endpoint counts', sorted(hist.items()), 'exceptional unordered pairs', len(exceptions))

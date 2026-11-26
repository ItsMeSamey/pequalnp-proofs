from composer import decide,edge
from itertools import product
import networkx as nx

g=nx.pappus_graph(); shore=nx.bipartite.color(g)
marks=[(0,1),(10,11),(14,15)]
cut=g.copy();cut.remove_edges_from(marks)
tips=sorted((v for e in marks for v in e),key=lambda v:(shore[v],next(i for i,e in enumerate(marks) if v in e)))
for i,j in [(i,j) for i in range(3) for j in range(3,6)]+[(-1,-1)]:
    ext=[(v,int(k in (i,j))) for k,v in enumerate(tips)]
    assert decide(cut,ext,shore)[0]=='SAT'
for red in marks:
    h=cut.subgraph(set(g)-set(red))
    rest=[e for e in marks if e!=red]
    fixed=[(v,c) for c,e in enumerate(rest) for v in e]
    for bits in product((0,1),repeat=2):
        ext=fixed+[(v,bits[i]^j) for i,u in enumerate(red) for j,v in enumerate(cut[u])]
        status,widths,sizes=decide(h,ext,shore)
        assert status=='UNSAT' and sorted(sizes)==[(8,8),(8,8)]
        assert max(widths)<=4
print('All 9 minority patterns and mono SAT. Three red choices and all holder orientations UNSAT; two order-eight eight-port blocks per instance.')
# Independently list full graph proper colorings and check restricted matching options.
def perfects(h):
    if not h:
        yield frozenset()
        return
    u=min(h,key=h.degree.__getitem__)
    for v in h[u]:
        for m in perfects(h.subgraph(set(h)-{u,v})):
            yield m|{edge(u,v)}

count=0
for m in perfects(g):
    h=g.copy();h.remove_edges_from(m)
    comp=list(nx.connected_components(h))
    count+=2**len(comp)
    if len(m.intersection(marks))!=1:continue
    ls=nx.line_graph(h); color=nx.bipartite.color(ls)
    b,c=[next(z for z in ls if edge(*z)==e) for e in marks if e not in m]
    assert nx.has_path(ls,b,c) and color[b]==color[c]
assert count==120
for red in marks:
    h=cut.subgraph(set(g)-set(red));ms=list(perfects(h))
    a=nx.Graph();a.add_edges_from(set.union(set(),*ms))
    assert len(ms)==4 and all(d==2 for _,d in a.degree()) and sorted(map(len,nx.connected_components(a)))==[8,8]
den2="200 011 011 011 011 110 101 011 101 101 110 110 011 101 101 110 110 101 011 020 101 011 110 110 002 110 101".split()
x=dict(zip(sorted(edge(*e) for e in g.edges),[tuple(map(int,s)) for s in den2],strict=True))
assert all(sum(z)==2 and all(0<=t<=2 for t in z) for z in x.values())
assert all(sum(x[edge(v,w)][c] for w in g[v])==2 for v in g for c in range(3))
assert all(x[e][c]==2 for c,e in enumerate(marks))

def cyclic_cut(g):
    n=len(g); adj=[sum(1<<w for w in g[v]) for v in range(n)]
    def cyclic(s):
        while s:
            t=sum(1<<v for v in range(n) if s>>v&1 and (s&adj[v]).bit_count()>=2)
            if s==t:return True
            s=t
        return False
    full=(1<<n)-1; best=7
    for s in range(1,1<<(n-1)):
        crossing=sum((adj[v]&~s).bit_count() for v in range(n) if s>>v&1)
        if crossing<best and cyclic(s) and cyclic(full^s):
            best,witness=crossing,s
    return best,[v for v in g if witness>>v&1]
connectivity,witness=cyclic_cut(g)
assert connectivity==6
print('120 named proper colorings, four allowed PM products per red choice. All 27 fractional edges and 54 vertex-color constraints validated. Cyclic connectivity',connectivity,'shore',witness)

# Independent global-matching check on arbitrary small cuts.
import random
from composer import extend_matching
rng=random.Random(319);counts={'SAT':0,'UNSAT':0,'UNKNOWN':0};maxfront=0
for n in range(3,8):
    for trial in range(7):
        while True:
            p=[rng.sample(range(n),n) for _ in range(3)]
            if all(len({q[i] for q in p})==3 for i in range(n)):break
        host=nx.Graph((i,n+q[i]) for q in p for i in range(n))
        r=min(3+trial%2,n)
        missing=rng.sample([(i,n+p[0][i]) for i in range(n)],r)
        host.remove_edges_from(missing)
        sh={v:int(v>=n) for v in host}
        for t in range(12):
            left=rng.choices((0,1),k=r)
            right=rng.sample(left,r) if t%3 else rng.choices((0,1),k=r)
            pp=[a for a,b in missing]+[b for a,b in missing]
            colors=left+right
            status,widths,_=decide(host,list(zip(pp,colors)),sh)
            truth=any(extend_matching(host,pp,colors,2,m) is not None for m in perfects(host))
            assert status=='UNKNOWN' or (status=='SAT')==truth
            assert max(widths,default=0)<=r
            counts[status]+=1;maxfront=max(maxfront,max(widths,default=0))
print('Random-cut control',counts,'largest wire frontier',maxfront)
probe=nx.Graph()
probe.add_edges_from([(0,4),(1,5),(2,6),(3,7),(0,6),(0,7),(1,6),(1,7)])
ext=[(v,c) for v in (4,5,2,3) for c in (0,1)]
result,ww,_=decide(probe,ext,{v:int(v>=4) for v in probe})
assert result=='SAT' and max(ww)==4
print('Four-wire frontier control',ww)

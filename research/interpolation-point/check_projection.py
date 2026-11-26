"""Direct origin projection checks. Small exhaustive algorithms serve as independent oracles."""
from itertools import product
from functools import lru_cache
from math import prod
from random import Random


class Ring:
    """Unramified degree-four ring, with residue field defined by X^4+X+1."""
    def __init__(self,k):
        self.k=k;self.mod=1<<k;self.zero=(0,0,0,0);self.one=(1,0,0,0)
    def n(self,a): return (a%self.mod,0,0,0)
    def add(self,a,b): return tuple((x+y)%self.mod for x,y in zip(a,b))
    def neg(self,a): return tuple(-x%self.mod for x in a)
    def mul(self,a,b):
        c=[0]*7
        for i,x in enumerate(a):
            for j,y in enumerate(b): c[i+j]+=x*y
        for i in range(6,3,-1): c[i-3]-=c[i];c[i-4]-=c[i]
        return tuple(x%self.mod for x in c[:4])
    def prod(self,values):
        ans=self.one
        for v in values: ans=self.mul(ans,v)
        return ans
    def sum(self,values):
        ans=self.zero
        for v in values: ans=self.add(ans,v)
        return ans
    def inv(self,a):
        assert any(c%2 for c in a)
        p=15*2**(4*(self.k-1))-1
        v=self.one
        while p:
            if p&1:v=self.mul(a,v)
            p//=2;a=self.mul(a,a)
        return v

def choices(n,edges):
    return product(*[[-1]+[e for e,uv in enumerate(edges) if u in uv] for u in range(n)])

def factors(state,edges,ws,b):
    return [b[v] for v,z in enumerate(state) if z<0]+[ws[e][2*int(state[u]==e)+int(state[v]==e)] for e,(u,v) in enumerate(edges)]

def matchings(n,edges):
    for s in range(1<<len(edges)):
        seen=set()
        for e,(u,v) in enumerate(edges):
            if s>>e&1:
                if u in seen or v in seen:break
                seen|={u,v}
        else: yield s,seen

def twin(n,edges,ds,hs,r):
    weighted={}
    for v in range(n): weighted[v,n+v]=(ds[v],0)
    for i in range(n,2*n):
        for j in range(i+1,2*n): weighted[i,j]=(r.one,0)
    for (u,v),h in zip(edges,hs): weighted[min(u,v),max(u,v)]=(h,1)
    @lru_cache(None)
    def rec(active):
        if not active:return {0:r.one}
        a=active[0];acc={}
        for v in active[1:]:
            w=weighted.get((a,v))
            if w is None:continue
            for j,c in rec(tuple(x for x in active[1:] if x!=v)).items():
                idx=j+w[1]
                acc[idx]=r.add(acc.get(idx,r.zero),r.mul(w[0],c))
        return acc
    return r.sum(r.mul(val,r.inv(r.n(prod(range(1,2*j,2))))) for j,val in rec(tuple(range(2*n))).items())

def shifted(n,edges,ws,b,t,r):
    ds=list(map(r.n,b));hs=[];bases=[]
    for (u,v),(a,c,bv,d) in zip(edges,ws):
        aa=r.add(r.n(a),t);ia=r.inv(aa);bases.append(aa)
        ds[u]=r.add(ds[u],r.mul(r.n(bv),ia))
        ds[v]=r.add(ds[v],r.mul(r.n(c),ia))
        hs.append(r.prod([r.add(r.mul(aa,r.n(d)),r.n(-bv*c)),ia,ia]))
    md=twin(n,edges,ds,hs,r)
    expected=r.sum(r.prod([ds[i] for i in range(n) if i not in seen]+[hs[i] for i in range(len(edges)) if s>>i&1]) for s,seen in matchings(n,edges))
    assert md==expected
    return r.mul(r.prod(bases),md)

def interpolate(points,values,r):
    total=r.zero
    for t,val in zip(points,values):
        l=r.prod(r.mul(r.neg(w),r.inv(r.add(t,r.neg(w)))) for w in points if w!=t)
        total=r.add(total,r.mul(l,val))
    return total

def valuation(x,p):
    return p if not x else min(p,(abs(x)&-abs(x)).bit_length()-1)
def check_triangle(n,edges,ws,b,p):
    cb=[valuation(x,p) for x in b]; ce=[[valuation(x,p) for x in row] for row in ws]
    base=sum(cb)+sum(row[0] for row in ce)
    expanded=[];weights=[]
    for e,((u,v),(a,c,bv,d)) in enumerate(zip(edges,ce)):
        expanded.extend([(u,n+e),(v,n+e),(u,v)])
        weights.extend([bv-a-cb[u],c-a-cb[v],d-a-cb[u]-cb[v]])
    h=min(p,min(base+sum(w for e,w in enumerate(weights) if s>>e&1) for s,_ in matchings(n+len(edges),expanded)))
    hist={};direct=0;all_costs=[]
    for state in choices(n,edges):
        f=factors(state,edges,ws,b)
        cost=sum(valuation(x,p) for x in f);all_costs.append(cost)
        direct+=prod(f)
        if cost<p:
            hist[cost]=hist.get(cost,0)+prod(x//2**valuation(x,p) for x in f)
    assert h==min(p,min(all_costs))
    result=sum(2**j*(v%2**(p-h)) for j,v in hist.items()) if h<p else 0
    assert result%2**p==direct%2**p

rng=Random(86)
graphs=[(3,[(0,1),(1,2),(0,2)]),(4,[(0,2),(0,3),(1,2),(1,3)])]
for i in range(40):
    n,edges=graphs[i%2];r=Ring(1+i%4)
    us=[[[rng.randrange(-2,4) for x in range(2)] for state in range(4)] for e in edges]
    b=[rng.randrange(-4,6) for v in range(n)]
    ws=[[sum(pair[2*a][x]*pair[2*c+1][x] for x in range(2)) for a,c in product(range(2),repeat=2)] for pair in us]
    physical=0
    for x in range(1<<len(edges)):
        tables=[]
        for v in range(n):
            ports=[(i,int(v==w)) for i,(u,w) in enumerate(edges) if v in (u,w)]
            modes=[prod(us[i][orientation+2*int(i==j)][(x>>i)&1] for i,orientation in ports) for j in [-1]+[i for i,o in ports]]
            tables.append(b[v]*modes[0]+sum(modes[1:]))
        physical+=prod(tables)
    assert physical==sum(prod(factors(s,edges,ws,b)) for s in choices(n,edges))
    points=[tuple((j>>i)&1 for i in range(4)) for j in range(2,3+len(edges))]
    vals=[shifted(n,edges,ws,b,t,r) for t in points]
    assert interpolate(points,vals,r)==r.n(physical)
    check_triangle(n,edges,ws,b,8)
print("40 full origin, shifted-extension, doubled-hafnian and valuation-floor checks passed")

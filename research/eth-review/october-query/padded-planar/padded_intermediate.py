"""Budgeted intermediate parity counts on recognized paired planar CNFs."""
from itertools import combinations


def _recognize(n,clauses):
    from collections import Counter,defaultdict
    if n<0:
        raise ValueError("invalid raw dimension")
    pos=Counter()
    used=set()
    raw={}
    for i,row in enumerate(clauses):
        if any(not 1<=abs(l)<=n for l in row):
            raise ValueError("invalid literal")
        if len(row)!=3 or len({abs(l) for l in row})!=3:
            return None
        key=tuple(sorted(row))
        if key in raw:
            return None
        raw[key]=i
        pos.update(l for l in row if l>0)
        used.update(abs(l) for l in row)
    base={v for v in used if pos[v]>=2}
    selectors={v for v in used if pos[v]==1}
    private=used-base-selectors
    adj=defaultdict(set)
    edges=defaultdict(dict)
    for row,i in raw.items():
        if max(row)<0:
            block={-l for l in row}
            for z in block&selectors: adj[z].update(block-{z})
            continue
        z=[l for l in row if l in selectors]
        ends=[l for l in row if abs(l) in base]
        if len(z)!=1 or len(ends)!=2 or (ends[0]>0)!=(ends[1]>0):
            return None
        e=tuple(sorted(map(abs,ends)))
        sign=ends[0]>0
        if sign in edges[e]:
            return None
        edges[e][sign]=(z[0],i)
    if not edges:
        return None
    expected=set()
    seen=set()
    blocks={}
    for (u,v),pair in edges.items():
        if len(pair)!=2:
            return None
        half=[]
        for sign,(z,i) in sorted(pair.items()):
            pad=adj[z]
            if len(pad)<2 or not pad<=private or seen&pad:
                return None
            seen.update(pad)
            ids=[z,*sorted(pad)]
            expected.add(i)
            triples=[]
            for a,b,c in combinations(range(len(ids)),3):
                key=tuple(sorted((-ids[a],-ids[b],-ids[c])))
                if key not in raw: return None
                triples.append((raw[key],(1<<a)|(1<<b)|(1<<c)))
                expected.add(raw[key])
            half.append((len(ids),i,sign,tuple(triples)))
        if half[0][0]!=half[1][0]:
            return None
        blocks[u,v]=half
    if seen!=private or expected!=set(raw.values()):
        return None
    import networkx as nx
    G=nx.Graph()
    G.add_nodes_from(base)
    G.add_edges_from(edges)
    if min(dict(G.degree()).values())<2 or not nx.is_connected(G) or not nx.check_planarity(G)[0]:
        return None
    return blocks,base,n-len(used)


def _basis(rows,rhs):
    basis={}
    for i,w in enumerate(rows):
        b=rhs>>i&1
        while w:
            j=w.bit_length()-1
            if j not in basis:
                basis[j]=w,b
                break
            u,c=basis[j]
            w^=u
            b^=c
        else:
            if b: return None
    return tuple(basis.values())


def _elimination(edges,vertices):
    pending=[set(e) for e in edges]
    order=[]
    burden=0
    live=set(vertices)
    while live:
        def scope(v):
            return set.union(*(s for s in pending if v in s))
        v=min(live,key=lambda x:(len(scope(x)),x))
        union=scope(v)
        burden+=1<<len(union)
        pending=[s for s in pending if v not in s]+[union-{v}]
        live.remove(v)
        order.append(v)
    return order,burden


def _contract(factors,order):
    for v in order:
        group=[(s,f) for s,f in factors if v in s]
        factors=[(s,f) for s,f in factors if v not in s]
        scope=sorted(set().union(*(s for s,f in group))-{v})
        out=[0]*(1<<len(scope))
        pos={w:i for i,w in enumerate([v]+scope)}
        for a in range(2<<len(scope)):
            term=1
            for s,f in group:
                key=sum(((a>>pos[w])&1)<<i for i,w in enumerate(s))
                term*=f[key]
            out[a>>1]+=term
        factors.append((tuple(scope),out))
    ans=1
    for s,f in factors:
        assert not s
        ans*=f[0]
    return ans


def count(n,clauses,checks,rhs=0,*,budget):
    """Return (count,stats); count=None denotes an unrecognized instance or budget miss."""
    clauses=tuple(tuple(c) for c in clauses)
    checks=tuple(checks)
    if budget<0 or not 0<=rhs<1<<len(checks) or any(not 0<=w<1<<len(clauses) for w in checks):
        raise ValueError("invalid budget or parity checks")
    shape=_recognize(n,clauses)
    if shape is None: return None,dict(status='unrecognized')
    basis=_basis(checks,rhs)
    if basis is None: return 0,dict(status='inconsistent')
    blocks,vertices,unused=shape
    order,contractions=_elimination(blocks,vertices)
    rank=len(basis)
    bound=(1<<rank)*(contractions+sum(4*(1<<d) for pair in blocks.values() for d,_,_,_ in pair))
    stats=dict(rank=rank,bound=bound,order=tuple(order))
    if bound>budget: return None,dict(stats,status='budget')
    total=0
    for char in range(1<<rank):
        mask=sign=0
        for i,(w,b) in enumerate(basis):
            if char>>i&1:
                mask^=w
                sign^=b
        factors=[]
        for e,pair in blocks.items():
            weights=[1]*4
            for d,main,positive,triples in pair:
                table=[0]*4
                observed=[s for i,s in triples if mask>>i&1]
                for a in range(1<<d):
                    parity=sum(a&s==s for s in observed)&1
                    for spin in range(4):
                        bad=int((spin==(0 if positive else 3)) and not(a&1))
                        table[spin]+=1-2*(parity^(bad&(mask>>main&1)))
                weights=[x*y for x,y in zip(weights,table)]
            factors.append((e,weights))
        total+=(1-2*sign)*_contract(factors,order)
    val,rem=divmod(total<<unused,1<<rank)
    assert not rem and 0<=val<=1<<n
    return val,dict(stats,status='counted')

from collections import Counter
from dataclasses import dataclass

@dataclass(frozen=True)
class Leaf:
    n:int
    clauses:tuple
    guard:int
    guard_row:int
    columns:tuple
    rungs:tuple
    rails:tuple

    def weight(self,word,pins=()):
        if not 0<=word<1<<len(self.clauses): raise ValueError("bad word")
        fixed={}
        for lit in pins:
            if not 1<=abs(lit)<=self.n: raise ValueError("bad pin")
            if abs(lit) in fixed and fixed[abs(lit)]!=(lit>0): return 0
            fixed[abs(lit)]=int(lit>0)
        g=1^(word>>self.guard_row&1)
        if fixed.get(self.guard,g)!=g: return 0
        def edge(f,a,b):
            i,z=f
            return sum(int(not(a or b or c))==(word>>i&1)
                       for c in ((fixed[z],) if z in fixed else (0,1)))
        def unary(i,s):
            a,b=s&1,s>>1
            x,y=self.columns[i]
            return int(fixed.get(x,a)==a and fixed.get(y,b)==b)*edge(self.rungs[i],a,b)
        def link(i,s,t):
            f,h=self.rails[i]
            return edge(f,s&1,t&1)*edge(h,s>>1,t>>1)
        total=0
        for start in range(4):
            dp=[0]*4
            dp[start]=unary(0,start)
            for i in range(1,len(self.columns)):
                dp=[unary(i,t)*sum(dp[s]*link(i-1,s,t) for s in range(4)) for t in range(4)]
            total+=sum(dp[s]*link(-1,s,start) for s in range(4))
        return total

def supplied_leaf(n,clauses):
    rows=tuple(tuple(row) for row in clauses)
    if any(len(row) not in (1,3) or len(set(row))!=len(row) or
           any(not 1<=x<=n for x in row) for row in rows): return None
    units=[i for i,row in enumerate(rows) if len(row)==1]
    cnt=Counter(x for row in rows for x in row)
    if len(units)!=1 or len(cnt)!=n: return None
    u=units[0]
    guard=rows[u][0]
    if cnt[guard]!=1: return None
    adj={x:set() for x in cnt if cnt[x]==3}
    factors={}
    for i,row in enumerate(rows):
        if i==u: continue
        sites=[x for x in row if x in adj]
        gates=[x for x in row if cnt[x]==1]
        if len(sites)!=2 or len(gates)!=1: return None
        a,b=sites
        key=frozenset(sites)
        if key in factors: return None
        adj[a].add(b)
        adj[b].add(a)
        factors[key]=(i,gates[0])
    L=len(adj)//2
    if L<4 or len(adj)!=2*L or any(len(v)!=3 for v in adj.values()): return None
    def f(a,b): return factors[frozenset((a,b))]
    for a in adj:
        for b in adj[a]:
            for c in adj[a]-{b}:
                for d in (adj[b]&adj[c])-{a}:
                    cols=[(a,b),(c,d)]
                    seen={a,b,c,d}
                    while len(cols)<L:
                        x,y=cols[-1]
                        p,q=cols[-2]
                        t,=adj[x]-{y,p}
                        v,=adj[y]-{x,q}
                        if t in seen or v in seen or v not in adj[t]: break
                        cols.append((t,v))
                        seen.update((t,v))
                    if len(cols)!=L: continue
                    x,y=cols[-1]
                    if a not in adj[x] or b not in adj[y]: continue
                    rails=tuple((f(p,cols[(i+1)%L][0]),f(q,cols[(i+1)%L][1]))
                                for i,(p,q) in enumerate(cols))
                    return Leaf(n,rows,guard,u,tuple(cols),tuple(f(p,q) for p,q in cols),rails)
    return None

@dataclass(frozen=True)
class Original:
    clauses:tuple
    leaf:Leaf
    circulant:tuple

def original(n,clauses):
    """Generated child uses unit first and real rows in their original order."""
    rows=tuple(tuple(row) for row in clauses)
    if not rows or any(len(row)!=3 or len(set(row))!=3 or
                       any(not 1<=x<=n for x in row) for row in rows): return None
    cnt=Counter(x for row in rows for x in row)
    g=max(cnt,key=cnt.get)
    real=[r for r in rows if g not in r]
    leaf=supplied_leaf(n,[(g,),*real])
    if leaf is None: return None
    spins={x for col in leaf.columns for x in col}
    v=len(spins)
    D=12*((n-1).bit_length()-1).bit_length()
    if D>=v-1: return None
    ng={x:set() for x in spins}
    for row in rows:
        if g not in row: continue
        x,y=(t for t in row if t!=g)
        if x not in spins or y not in spins or y in ng[x]: return None
        ng[x].add(y)
        ng[y].add(x)
    if any(len(t)!=D for t in ng.values()): return None
    if v==D+2:
        pairs={tuple(sorted((x,next(iter(spins-ng[x]-{x}))))) for x in spins}
        order=[x for x,y in sorted(pairs)]+[y for x,y in sorted(pairs)]
    else:
        closed={x:ng[x]|{x} for x in spins}
        near={x:[y for y in spins if len(closed[x]^closed[y])==2] for x in spins}
        if any(len(t)!=2 for t in near.values()): return None
        order=[min(spins)]
        while len(order)<v:
            opts=[x for x in near[order[-1]] if x not in order]
            if not opts: return None
            order.append(min(opts))
    for i,x in enumerate(order):
        if ng[x]!={order[(i+j)%v] for j in range(-D//2,D//2+1) if j}: return None
    return Original(rows,leaf,tuple(order))

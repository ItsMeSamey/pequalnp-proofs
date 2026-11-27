"""Complete physical shell enumeration for two high pins with exactly one optional leaf."""
from itertools import combinations,product
from collections import Counter
from degree_five_active_shells import root, key, glue, parity


def grow(deg, T, budget):
    k = len(deg)
    full = (1 << k) - 1
    opts = [[f - d for f in (1, 3, 5) if f >= d] for d in deg]
    types = [t for t in range(1, 1 << k) if not any(parity(t & u) for u in T[t])]
    pairs = {}
    for t, h in product(types, repeat=2):
        forbidden = {
            1 ^ parity(t & u) for u in T[t ^ h] if parity(t & u) == parity(h & u)
        }
        pairs[t, h] = set((0, 1)) - forbidden

    def visit(d, ts, start):
        if any(d):
            for j in range(start, len(types)):
                t = types[j]
                e = [n - ((t >> i) & 1) for i, n in enumerate(d)]
                if min(e) >= 0 and all(pairs[t, h] for h in ts):
                    yield from visit(e, ts + [t], j)
            return
        if not ts:
            return
        l = len(ts)

        sig = [0] * (1 << l)
        for s in range(1, 1 << l):
            lo = s & -s
            sig[s] = sig[s ^ lo] ^ ts[lo.bit_length() - 1]
        old = T[sig[-1]]
        if old.get(full) != 1 or any(
            u != full and not any(parity((full ^ u) & t) for t in ts) for u in old
        ):
            return
        ext = [0] * l
        optional = []
        for i, j in combinations(range(l), 2):
            p = pairs[ts[i], ts[j]]
            if len(p) == 2:
                optional.append((i, j))
            elif 1 in p:
                ext[i] |= 1 << j
                ext[j] |= 1 << i
        yield from edge_sweep(l, ts, sig, ext, optional, T)

    for ds in product(*opts):
        leaves=sum(old+extra==1 for old,extra in zip(deg,ds))
        if any(ds) and leaves<=budget:
            for next_data in visit(ds, [], 0):
                yield (*next_data,budget-leaves)


def edge_sweep(l, ts, sig, ext, optional, T, idx=0):
    ds = [ext[i].bit_count() + t.bit_count() for i, t in enumerate(ts)]
    if max(ds) > 5 or not any(d < 5 for d in ds):
        return
    if idx < len(optional):
        i, j = optional[idx]
        yield from edge_sweep(l, ts, sig, ext, optional, T, idx + 1)
        ext[i] ^= 1 << j
        ext[j] ^= 1 << i
        yield from edge_sweep(l, ts, sig, ext, optional, T, idx + 1)
        ext[i] ^= 1 << j
        ext[j] ^= 1 << i
        return
    J = [j for j, d in enumerate(ds) if d < 5]
    keep = sum(1 << j for j in J)

    def packed(x):
        return sum(((x >> j) & 1) << i for i, j in enumerate(J))

    P = [{} for _ in range(1 << len(J))]
    for s, t in enumerate(sig):
        p = packed(s)
        for u, c in T[t].items():
            err = s & sum(
                (1 ^ parity(u & ts[j]) ^ parity(s & ext[j])) << j for j in range(l)
            )
            if err == 0:
                return
            if err & ~keep:
                continue
            e = packed(err)
            for v in range(len(P)):
                if p & v == e:
                    P[v][p] = min(2, c + P[v].get(p, 0))
    dd = [ds[j] for j in J]
    mask = sum((1 ^ (d & 1)) << j for j, d in enumerate(dd))
    if P[mask].get((1 << len(J)) - 1) != 1:
        return
    yield dd, P, tuple(ts), tuple(ext)


def starts():
 for c in range(1,6):
  vals=[d-c for d in [3,5] if d>=c]
  for a,b in product(vals,repeat=2):
   if a>b:continue
   n=2+a+b+c
   A=tuple(range(2,2+a));B=tuple(range(2+a,2+a+b));C=tuple(range(2+a+b,n))
   rows=[0]*n
   def flip(i,j):
    rows[i]^=1<<j;rows[j]^=1<<i
   for i in A+C:flip(0,i)
   for j in B+C:flip(1,j)
   for i,j in product(A,B):flip(i,j)
   if max(r.bit_count() for r in rows)>5:continue
   edges=[(i,j) for i,j in combinations(range(2,n),2) if not (rows[i]>>j&1)]
   def dfs(i):
    if i<len(edges):
     u,v=edges[i]
     yield from dfs(i+1)
     if max(rows[u].bit_count(),rows[v].bit_count())<5:
      flip(u,v);yield from dfs(i+1);flip(u,v)
     return
    if any(rows[v].bit_count() not in (3,5) for v in C):return
    ports=[u for u in A+B if rows[u].bit_count()<5]
    yield tuple(rows),ports
   yield from dfs(0)

def terminals(deg,T,budget):
    k=len(deg)
    allports=(1<<k)-1
    alltypes=range(1,1<<k)
    single={t for t in alltypes if not any(parity(t&u) for u in T[t])}
    pair={}
    for t,h in product(alltypes,repeat=2):
        pair[t,h]={0,1}-{1^parity(t&u) for u in T[t^h] if parity(t&u)==parity(h&u)}
    def build(left,ts,start):
        if not any(left):
            if ts:yield ts
            return
        for t in range(start,1<<k):
            if ts and (t not in single or ts[0] not in single):continue
            if len(ts)>=2 and (not pair[ts[0],ts[1]] or any(not pair[h,t] for h in ts)):continue
            remain=tuple(v-(t>>i&1) for i,v in enumerate(left))
            if min(remain)>=0:yield from build(remain,ts+(t,),t)
    for ds in product(*[[v-d for v in (1,3,5) if v>=d] for d in deg]):
        used=sum(d+x==1 for d,x in zip(deg,ds))
        if used>budget:continue
        for ts in build(ds,(),1):
            m=len(ts)
            sig=[0]*(1<<m)
            for s in range(1,len(sig)):
                bit=s&-s
                sig[s]=sig[s^bit]^ts[bit.bit_length()-1]
            if T[sig[-1]].get(allports)!=1:continue
            internal=[0]*m;optional=[]
            for i,j in combinations(range(m),2):
                allowed=pair[ts[i],ts[j]] if m>2 else {0,1}
                if allowed=={1}:
                    internal[i]|=1<<j;internal[j]|=1<<i
                elif len(allowed)==2:optional.append((i,j))
                elif not allowed:raise AssertionError
            def finish(index):
                ds2=[r.bit_count()+t.bit_count() for r,t in zip(internal,ts)]
                if max(ds2)>5:return
                if index<len(optional):
                    i,j=optional[index]
                    yield from finish(index+1)
                    internal[i]^=1<<j;internal[j]^=1<<i
                    yield from finish(index+1)
                    internal[i]^=1<<j;internal[j]^=1<<i
                    return
                if any(d not in (1,3,5) for d in ds2) or used+ds2.count(1)!=budget:return
                for s,v in enumerate(sig):
                    for u in T[v]:
                        if s==len(sig)-1 and u==allports:continue
                        if all(not (s>>j&1) or parity(u&ts[j])^parity(s&internal[j]) for j in range(m)):
                            return
                yield ts,tuple(internal)
            yield from finish(0)


def only_full(rows):
    f=(1<<len(rows))-1
    return all(r.bit_count() in (1,3,5) for r in rows) and not any(all(
        not(s>>j&1) or parity(r&s) for j,r in enumerate(rows)) for s in range(3,f,4))


def main():
    queue=[];examples={};counts=Counter()
    def record(rows):
        assert only_full(rows) and sum(r.bit_count()==1 for r in rows)==1
        counts[len(rows)]+=1
        examples.setdefault(len(rows),tuple(rows))
    for rows,ports in starts():
        d,t=root(dict(rows=rows,ports=ports))
        if t[0]:
            if sum(r.bit_count()==1 for r in rows)==1 and only_full(rows):record(rows)
        else:
            if ports:queue.append((d,t,rows,ports,1))
    print('closed',dict(counts),flush=True)
    while queue:
        levels={};end={};later=[]
        cap=max(len(rows)+sum(5-x for x in d) for d,t,rows,ports,b in queue)
        for d,t,rows,ports,b in queue:
            token=key(d,t),b
            if token not in levels:
                levels[token]=list(grow(d,t,b));end[token]=list(terminals(d,t,b))
            for inc,ext in end[token]:record(glue(rows,ports,inc,ext)[0])
            for dd,tt,inc,ext,bb in levels[token]:
                graph,newports=glue(rows,ports,inc,ext)
                later.append((dd,tt,graph,newports,bb))
        print('prefixes',len(queue),'states',len(levels),'cap',cap,'cumulative labelled',dict(counts),flush=True)
        queue=later
    print('examples',examples,flush=True)


if __name__=='__main__':main()

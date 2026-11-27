"""Independent physical terminal sweep using a direct old-word response model.
Nonterminal transitions and initial cores are shared with the candidate implementation.
"""
from collections import Counter
from itertools import product,combinations
from types import SimpleNamespace
import networkx as nx
from single_leaf_high_pin_shells import starts,grow
from degree_five_active_shells import root,key,glue
from degree_five_raw_shell_check import ones,expand
from edge_torso_atlas_check import witnesses

def terminal(old,budget):
    n=len(old.rows);k=len(old.ports);oldfull=(1<<n)-1
    opts=[tuple(f-d for f in (1,3,5) if f>=d) for d in old.degrees]
    alltypes=list(range(1,1<<k))
    single={}
    for t in alltypes:
        single[t]=[w for w,u in old.ok[t] if (u&t).bit_count()%2]
    def rowsets(ds,lo,prefix):
        if not any(ds):
            if prefix:yield prefix
            return
        for t in range(lo,1<<k):
            residual=tuple(d-(t>>i&1) for i,d in enumerate(ds))
            if min(residual)<0:continue
            if (prefix or any(residual)) and single[t]:continue
            yield from rowsets(residual,t,prefix+(t,))
    for ds in product(*opts):
        used=sum(d+x==1 for d,x in zip(old.degrees,ds))
        if used>budget:continue
        for ts in rowsets(ds,1,()):
            m=len(ts)
            if m>1 and any(single[t] for t in ts):continue
            # With every new vertex selected, preserving each new-site incoming bit
            # must force the full old word; independent of all new internal edges.
            sigma=0
            for t in ts:sigma^=t
            if [w for w,u in old.ok[sigma]
                if all(((~u)&t).bit_count()%2==0 for t in ts)]!=[oldfull]:continue
            rr=list(old.rows)+[expand(t,old.ports) for t in ts]
            for i,t in enumerate(ts):
                for b in ones(t):rr[old.ports[b]]|=1<<(n+i)
            free=[]
            for i,j in combinations(range(m),2):
                opts2=[0,1]
                if m>2:
                    for bit in (0,1):
                        if any((bit+(u&ts[i]).bit_count())%2 and (bit+(u&ts[j]).bit_count())%2
                               for w,u in old.ok[ts[i]^ts[j]]):
                            opts2.remove(bit)
                if not opts2:break
                if opts2==[1]:
                    rr[n+i]|=1<<(n+j);rr[n+j]|=1<<(n+i)
                if len(opts2)==2:free.append((n+i,n+j))
            else:
                def attach(pos):
                    if any(v.bit_count()>5 for v in rr[n:]):return
                    if pos==len(free):
                        if all(v.bit_count() in (1,3,5) for v in rr[n:]) and used+sum(v.bit_count()==1 for v in rr[n:])==budget:
                            # Enumerate all native words by new-layer subset and actual
                            # old words. Unlike an unstructured power-set scan, this
                            # also remains cheap on the longer losing extensions.
                            for s in range(1<<m):
                                drift=0
                                for j in ones(s):drift^=ts[j]
                                for w,u in old.ok[drift]:
                                    raw=w|(s<<n)
                                    if raw!=(1<<len(rr))-1 and all((rr[n+j]&raw).bit_count()%2 for j in ones(s)):return
                            
                            yield tuple(ts),tuple(x>>n for x in rr[n:])
                        return
                    i,j=free[pos]
                    yield from attach(pos+1)
                    rr[i]^=1<<j;rr[j]^=1<<i
                    yield from attach(pos+1)
                    rr[i]^=1<<j;rr[j]^=1<<i
                yield from attach(0)


def census():
    q=[]
    types=[]
    def record(rows):
        assert witnesses(rows,0,1)
        assert sum(r.bit_count()==1 for r in rows)==1
        g=nx.Graph()
        for i,r in enumerate(rows):
            g.add_node(i,pin=i<2)
            for j in range(i):
                if r>>j&1:g.add_edge(i,j)
        for h,series in types:
            if nx.is_isomorphic(g,h,node_match=lambda a,b:a==b):
                series.append(tuple(rows));return
        types.append((g,[tuple(rows)]))
    for rows,ports in starts():
        d,t=root(dict(rows=rows,ports=ports))
        if t[0]:
            if all(r.bit_count()%2 for r in rows) and sum(r.bit_count()==1 for r in rows)==1 and witnesses(rows,0,1):
                record(rows)
        elif ports:q.append((d,t,rows,ports,1))
    while q:
        cache={}
        nxt=[]
        for d,t,rows,ports,b in q:
            token=(key(d,t),b)
            if token not in cache:
                k=len(d);f=(1<<k)-1
                drift=sum((1^(x%2))<<j for j,x in enumerate(d))
                ok=[]
                for v,row in enumerate(t):
                    entries=[]
                    for u,multiplicity in row.items():
                        full=(u==f and v==drift)
                        if full:entries.append((f,u))
                        if multiplicity>int(full):entries.append((0,u))
                    ok.append(entries)
                # Terminal() treats only its all-ones mask as the full witness.
                old=SimpleNamespace(rows=[0]*k,ports=range(k),degrees=d,ok=ok)
                cache[token]=list(terminal(old,b)),list(grow(d,t,b))
            end,extensions=cache[token]
            for inc,ext in end:
                record(glue(rows,ports,inc,ext)[0])
            for dd,tt,inc,ext,bb in extensions:
                rr,j=glue(rows,ports,inc,ext)
                nxt.append((dd,tt,rr,j,bb))
        print(len(q),len(cache),sum(len(s) for _,s in types),flush=True)
        q=nxt
    for _,hits in types:print(len(hits),hits[0])
    print('types',len(types))
if __name__=='__main__':census()

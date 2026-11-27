"""Original-graph checks with contacts more than 128 canonical P/S steps apart."""
from collections import deque, Counter
from itertools import combinations
from pathlib import Path
import sys
sys.path.insert(0,'/workspace/scratch/pnp-general-separation')
from degree_five_periodic_prime import chain
from leaf_cap_support_check import reduce,bits

def trial(periods=76, outer_triangle=False):
 G,p,q=chain(periods)
 if outer_triangle:
    u=len(G);leaf=u+1;G.extend([0,0])
    for a,b in ((p,q),(u,p),(u,q),(u,leaf)):
        G[a]|=1<<b;G[b]|=1<<a
    p,q=leaf,p
 names=(p,q);cur=G;stages=[]; history=set()
 while len(G)-len(history)>8:
    if cur[p].bit_count()!=1:p,q=q,p
    typ,(np,nq),gone,H=reduce(cur,p,q)
    assert typ in ('paired','common')
    stages.append((p,q,typ,cur,history.copy()))
    history.update(bits(gone))
    cur=H;p,q=np,nq
 counts=Counter()
 # A last previously introduced neighbor U of remote X is required; orient actual introductions.
 p,q=names; introduced={p,q}; intro={p:0,q:0}; older={}
 for i,(p,q,typ,H,_) in enumerate(stages):
    u,=bits(H[p]); v=bits(H[q])[0] if typ=='paired' else bits(H[q]&H[u])[0]
    for w in (u,v):
        if w in introduced:continue
        prior=set(bits(G[w]))&introduced
        assert prior
        older[w]=min(prior);intro[w]=i;introduced.add(w)
 for i,(p,q,typ,H,prev) in enumerate(stages[:3]):
    u,=bits(H[p])
    for x in sorted(older):
        if intro[x]-i<130 or G[x].bit_count()>3:continue
        U=older[x]
        for touch in ((p,), (p,q), (u,), (u,q)):
            if p not in touch and typ!='common':continue
            if G[x].bit_count()+len(touch)>5 or any(G[t].bit_count()>=5 for t in touch):continue
            fixed=set(touch)
            # Optional further contacts across the local physical neighborhood.
            ball={q};front={q}
            for _ in range(4):
                front=set().union(*(set(bits(H[t])) for t in front))-ball if front else set()
                ball|=front
            for z in [None]+sorted(ball-{p,q,u}):
                added=fixed if z is None else fixed|{z}
                if G[x].bit_count()+len(added)>5 or any(G[t].bit_count()>=5 for t in added):continue
                def xn(t):return bool(G[x]>>t&1) or t in added
                opt=False
                if p in added and q in added:
                    select={p,q,x,U}
                elif p not in added and q not in added:
                    select={p,q,u,x}
                else:
                    forbidden={p,u};select={p,x}
                    if p not in added:
                        v,=bits(H[u]&H[q]);forbidden.add(v);select.add(u)
                    dq=deque([[q]]);seen={q}
                    while dq:
                        path=dq.popleft();end=path[-1]
                        if end!=q and not xn(end):break
                        for t in bits(H[end]):
                            if t not in seen|forbidden:
                                dq.append(path+[t]);seen.add(t)
                    else:raise AssertionError('no path')
                    assert len(path)<=5
                    select.update(path)
                    if sum(xn(t) for t in select)%2==0:select.add(U)
                select|=prev
                assert set(names)<=select
                for t in select:
                    deg=sum(bool(G[t]>>s&1) or (t==x and s in added) or (s==x and t in added) for s in select)
                    assert deg%2,(i,typ,x,touch,z,t,deg)
                counts[typ,tuple('p' if t==p else 'q' if t==q else 'u' for t in touch)]+=1
 print('vertices',len(G),'canonical layers',len(stages),'checked',sum(counts.values()),counts)
if __name__=='__main__':trial();trial(outer_triangle=True)

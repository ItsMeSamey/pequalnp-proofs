"""Finite regular-path oracle with the graph transformation and physical mask recovery."""
from itertools import combinations
from random import Random


def involutions(ids):
    if not ids:
        yield {}
        return
    x,*rest=ids
    for sub in involutions(rest):yield {**sub,x:x}
    for i,y in enumerate(rest):
        for sub in involutions(rest[:i]+rest[i+1:]):yield {**sub,x:y,y:x}


def build(f,n):
    ahead=lambda i:3*(i//3)+(i+1)%3
    sigma=[f[ahead(i)] for i in range(n)]
    mate={v:f[v] for v in range(n)}
    incoming=list(range(n));outgoing=list(range(n));arcs=[]
    def pair(x,y,mx,my,tag,mtag):
        j=len(arcs)
        arcs.extend([(x,y,j+1,tag),(mx,my,j,mtag)])
    for v in range(n):
        if f[v]==v:
            w=len(mate);mate[v]=w;mate[w]=v;outgoing[v]=w
            pair(v,w,v,w,None,None)
    for i in range(n):
        j=ahead(i)
        pair(outgoing[i],incoming[sigma[i]],outgoing[j],incoming[sigma[ahead(j)]],(i,0),(j,1))
    return sigma,mate,incoming,outgoing,arcs


def solve(model,r,s):
    sigma,mate,I,O,base=model
    if r==s:return 0
    R,S=O[r],I[s]
    a=len(mate);b=a+1
    arcs=base.copy()
    k=len(arcs)
    arcs.extend([(a,R,k+1,None),(mate[R],b,k,None),
                 (S,b,k+3,None),(a,mate[S],k+2,None)])
    adj=[[] for _ in range(b+1)]
    for i,(u,v,m,tag) in enumerate(arcs):adj[u].append(i)
    def search(u,nodes,used):
        if u==b:return []
        for i in adj[u]:
            _,v,m,_=arcs[i]
            if v in nodes or m in used:continue
            suffix=search(v,nodes|{v},used|{i})
            if suffix is not None:return [i]+suffix
        return None
    P=search(a,{a},set())
    if P is None:return None
    if P[0]==k+3:P=[arcs[i][2] for i in reversed(P)]
    # Loop erase after projection, retaining the actual directed turn labels.
    path=[r];turns=[]
    for i in P:
        tag=arcs[i][3]
        if tag is None:continue
        u,h=tag;v=sigma[3*(u//3)+(u%3+h)%3]
        if u!=path[-1]:raise AssertionError((u,path))
        if v in path:
            j=path.index(v);path=path[:j+1];turns=turns[:j]
        else:path.append(v);turns.append((u//3,h))
    if path[-1]!=s:raise AssertionError(path)
    bits=dict(turns)
    if any(bits[g]!=h for g,h in turns):raise AssertionError(turns)
    return sum(h<<g for g,h in bits.items())


def labels(sigma,m):
    out={}
    for u in range(len(sigma)):
        seed=u
        while u not in out:
            out[u]=seed
            u=sigma[3*(u//3)+(u%3+(m>>(u//3)&1))%3]
    return out


if __name__=='__main__':
    rng=Random(32971);models=total=yes=0
    for g in (1,2,3):
        n=3*g;domain=list(involutions(list(range(n))))
        for f in (domain if g<3 else rng.sample(domain,120)):
            model=build(f,n);oracle=[labels(model[0],m) for m in range(1<<g)]
            models+=1
            for r in range(n):
                for s in range(n):
                    m=solve(model,r,s)
                    truth=any(L[r]==L[s] for L in oracle)
                    if (m is not None)!=truth or (truth and oracle[m][r]!=oracle[m][s]):
                        raise AssertionError((f,r,s,m))
                    yes+=truth;total+=1
    print(models,'models;',total,'ordered queries;',yes,'witnesses;',total-yes,'negatives')

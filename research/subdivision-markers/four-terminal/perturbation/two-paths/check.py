"""Exact small-tree enumeration for the contraction, L-shape table, and separator cases."""
from itertools import combinations
from random import Random

def trees(n,edges):
    for ids in combinations(range(len(edges)),n-1):
        rows=[[] for _ in range(n)]
        for i in ids:
            a,b=edges[i][:2]
            rows[a].append((b,i));rows[b].append((a,i))
        parent={0:None};todo=[0]
        for v in todo:
            for w,j in rows[v]:
                if w not in parent:parent[w]=(v,j);todo.append(w)
        if len(todo)==n:
            yield todo,parent,ids

def outcomes(n,edges,d):
    # Contracted terminals are s=0,t=1,w=2. Demand d is even.
    found=set()
    for order,par,ids in trees(n,edges):
        ps={0:0};ss={0:0}
        for v in order[1:]:
            u,j=par[v]
            ps[v]=ps[u]^edges[j][2];ss[v]=ss[u]^edges[j][3]
        spin=sum(ps[v] for v in range(n) if d>>v&1)%2
        found.add(ps[1]+2*ss[1]+4*spin)
    return found

def expanded(n,edges,delta,D):
    # Move type-one incidences at w to v=n, and add e=(2,n) of gain delta.
    E=[(n if h and a==2 else a,n if h and b==2 else b,g^(delta*h)) for a,b,g,h in edges]
    E.append((2,n,delta))
    found=set()
    for order,par,ids in trees(n+1,E):
        if len(E)-1 not in ids:continue
        ps={0:0};used={0:False}
        for v in order[1:]:
            u,j=par[v];ps[v]=ps[u]^E[j][2];used[v]=used[u]^(j==len(E)-1)
        spin=sum(ps[v] for v in range(n+1) if D>>v&1)%2
        found.add(ps[1]+2*used[1]+4*spin)
    return found

def obstruction():
    pairs=[(0,4),(3,5),(3,4),(0,5),(2,3),(2,5),(1,2),(4,5),(1,4),(0,3)]
    edges=[(a,b,int(j in (0,7,9)),int(j==4)) for j,(a,b) in enumerate(pairs)]
    both=outcomes(6,edges,5)
    assert both==set(range(8))-{3}
    assert expanded(6,edges,0,5)==both
    for a,b in combinations(range(1,8),2):
        image={( (z&a).bit_count()%2,(z&b).bit_count()%2) for z in both}
        assert ((3&a).bit_count()%2,(3&b).bit_count()%2) in image
    return edges

def reach(n,edges,root,forbid):
    seen={root};todo=[root]
    for v in todo:
        for a,b,*_ in edges:
            if v==a or v==b:
                w=a^b^v
                if w not in forbid and w not in seen:seen.add(w);todo.append(w)
    return seen

def separator_test(n,edges,d):
    components=reach(n,edges,0,{2}),reach(n,edges,1,{2})
    assert not (components[0]&components[1])
    # Restrict nodes to the two non-w sides: here all vertices lie there or at w.
    assert set.union(*components,{2})==set(range(n))
    direct=set()
    # The table concerns mandatory-D closing paths, which may differ from a
    # full ambient-tree spin when off-path D can be omitted. Keep a bit for
    # such automatic successes separately.
    def path_rows(E):
        results=set()
        def walk(v,seen,g,h,score):
            if v==1:
                missing=bool(d&~seen)
                results.add((g,h,score,missing))
                return
            for a,b,sg,sh in E:
                if v not in (a,b):continue
                w=a^b^v
                if seen>>w&1:continue
                y=g^sg
                walk(w,seen|1<<w,y,h^sh,score^(y*((d>>w)&1)))
        walk(0,1,0,0,0)
        return results
    want={(g,s,m) for g,h,s,m in path_rows(edges) if h==1}
    for alpha in (0,1):
        filt=[]
        for e in edges:
            a,b,g,h=e
            if 2 in (a,b):
                u=a^b^2
                if h!=alpha^(u in components[1]):continue
            filt.append(e)
        direct.update((g,s,m) for g,h,s,m in path_rows(filt))
    assert direct==want

if __name__=='__main__':
    rng=Random(97813);obstruction()
    for _ in range(650):
        n=rng.randint(3,7)
        pairs=[(rng.randrange(i),i) for i in range(1,n)]
        pairs += [tuple(rng.sample(range(n),2)) for _ in range(rng.randrange(5))]
        E=[(a,b,rng.randrange(2),rng.randrange(2) if 2 in (a,b) else 0) for a,b in pairs]
        D=rng.randrange(1<<(n+1)); D^=D.bit_count()%2
        delta=rng.randrange(2)
        d=(D&((1<<n)-1))^((1<<2)*((D>>n)&1))
        before=expanded(n,E,delta,D)
        after={z^(4*(delta*((D>>n)&1))) for z in outcomes(n,E,d)}
        assert before==after
    for _ in range(400):
        k=rng.randint(1,4);l=rng.randint(1,4)
        A=[0]+list(range(3,k+2));B=[1]+list(range(k+2,k+l+1));n=k+l+1
        E=[]
        for side in (A,B):
            for v in side:E.append((v,2,rng.randrange(2),rng.randrange(2)))
            for a,b in combinations(side,2):
                if abs(side.index(a)-side.index(b))==1 or rng.randrange(2):E.append((a,b,rng.randrange(2),0))
        d=rng.randrange(1<<n)
        separator_test(n,E,d)
    print('650 full tree-table contractions; 400 separator path tables; seven-of-eight obstruction')

"""Compare all guard states with all graphic witnesses and their small supports."""
from random import Random

def check_graph(n, edges, cycle_tags, cut_tags, t):
    adj=[[] for _ in range(n)]
    base=[]; chord=[]
    def tree_path(a,b):
        seen={a}; stack=[(a,0)]
        while stack:
            v,p=stack.pop()
            if v==b:
                return p
            for w,edge in adj[v]:
                if w not in seen:
                    seen.add(w); stack.append((w,p^(1<<edge)))
        return None
    for e,(a,b) in enumerate(edges):
        path=tree_path(a,b)
        if path is None:
            base.append(e); adj[a].append((b,e)); adj[b].append((a,e))
        else:
            chord.append(e)
    fundamental=[tree_path(*edges[e]) for e in chord]
    def label(mask,tags):
        result=0
        for i,v in enumerate(tags):
            if mask>>i&1:
                result^=v
        return result
    guard=set()
    for p in range(1<<len(base)):
        ps=sum((p>>j&1)<<e for j,e in enumerate(base))
        cut=ps|sum(((ps&path).bit_count()%2)<<e for path,e in zip(fundamental,chord))
        for q in range(1<<len(chord)):
            cyc=0
            for j,(path,e) in enumerate(zip(fundamental,chord)):
                if q>>j&1:
                    cyc^=path^(1<<e)
            if not cyc&cut:
                guard.add(label(cyc,cycle_tags)^label(cut,cut_tags))
    cycles=[]
    for C in range(1<<len(edges)):
        odd=V=0; sets=list(range(n))
        def find(x):
            while x!=sets[x]:
                x=sets[x]
            return x
        rank=0
        for e,(a,b) in enumerate(edges):
            if C>>e&1:
                odd^=(1<<a)^(1<<b); V|=(1<<a)|(1<<b)
                u,v=find(a),find(b)
                if u!=v:
                    sets[v]=u; rank+=1
        if not odd:
            cycles.append((C,V,C.bit_count()-rank,label(C,cycle_tags)))
    all_labels=set(); compressed=set(); weights=[0]*n
    for (u,v),b in zip(edges,cut_tags):
        weights[u]^=b; weights[v]^=b
    for S in range(1<<n):
        D=sum((((S>>u)^(S>>v))&1)<<e for e,(u,v) in enumerate(edges))
        dc=label(D,cut_tags)
        assert dc==label(S,weights)
        for C,V,beta,cc in cycles:
            if C&D:
                continue
            all_labels.add(dc^cc)
            if beta<=t and (S&~V).bit_count()<=t:
                compressed.add(dc^cc)
    assert guard==all_labels==compressed

rng=Random(66)
for i in range(300):
    n=rng.randrange(1,7); m=rng.randrange(10); t=rng.randrange(1,4)
    E=[(rng.randrange(n),rng.randrange(n)) for _ in range(m)]
    check_graph(n,E,[rng.randrange(1<<t) for _ in E],[rng.randrange(1<<t) for _ in E],t)
# Check undirected mod-four encoding with all endpoint/interior weights on short paths.
for n in range(2,9):
    for bits in range(1<<n):
        V=[(bits>>i)&1 for i in range(n)]
        assert sum(a+b for a,b in zip(V,V[1:]))%4==(V[0]+V[-1]+2*sum(V[1:-1]))%4
print("Verified 300 multigraph instances and 508 binary-labelled paths.")

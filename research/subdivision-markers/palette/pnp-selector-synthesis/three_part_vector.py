"""Direct vector-valued root-demand algorithm for the indexed cographic wedge span."""
from itertools import combinations,permutations
from planar_moment_certificate import CertifiedDual


def basis(n,edges,order=None, sites=None, observation=None):
    """Default computes full W. observation[(i,j)] is the bit-vector image of e_i∧e_j."""
    dual=CertifiedDual(n,tuple(tuple(edge) for edge in edges));
    neighbors=[{w for w,_ in ring if w!=v} for v,ring in enumerate(dual.graph)]
    if order is None:
        live=set(range(n));found=[]
        while live:
            for v in sorted(live):
                if all(z in neighbors[w] for w,z in combinations(neighbors[v]&live,2)):
                    break
            else:raise ValueError("nonchordal graph")
            live.remove(v);found.append(v)
        order=found
    order=tuple(order)
    if sorted(order)!=list(range(n)):raise ValueError("invalid order")
    rank={v:i for i,v in enumerate(order)}
    later={v:sorted(w for w in neighbors[v] if rank[w]>rank[v]) for v in order}
    if any(z not in neighbors[w] for v in order for w,z in combinations(later[v],2)):
        raise ValueError("not a perfect elimination order")
    if sites is not None and observation is not None:raise ValueError("choose a single projection")
    if sites is None:sites=range(len(dual.edges))
    sites=tuple(sites)
    if len(set(sites))!=len(sites) or any(i<0 or i>=len(dual.edges) for i in sites):
        raise ValueError("invalid projected coordinates")
    if observation is None:
        columns={(i,j):1<<s for s,(i,j) in enumerate(combinations(sites,2))}
    else:
        columns=dict(observation)
        for (i,j),value in columns.items():
            if not 0<=i<j<len(dual.edges) or not isinstance(value,int) or value<0:
                raise ValueError("invalid observation column")
    width=max((v.bit_length() for v in columns.values()),default=0)
    if not width:return
    coefficients={}
    def add(target,key,value):
        result=target.get(key,0)^value
        if result:target[key]=result
        else:target.pop(key,None)
    for (i,j),column in columns.items():
        for e,f in ((i,j),(j,i)):
            for u in dual.edges[e][:2]:
                for v in dual.edges[f][:2]:
                    if u!=v:add(coefficients,(1<<u,1<<v),column)
    for c in (0,1):
        for bit in (1,2):
            prev=coefficients;coefficients=prev.copy()
            for v,q in enumerate(dual.charge):
                if bit&q:
                    vb=1<<v
                    for (a,b),value in prev.items():
                        x,y=(a|vb,b) if c==0 else (a,b|vb)
                        if not x&y:add(coefficients,(x,y),value)
    if not coefficients:return
    ids={(0,0):0};terms=[(0,0)]
    def term_id(t):
        if t not in ids:ids[t]=len(terms);terms.append(t)
        return ids[t]
    def packed(vector):
        out=0
        for t,value in vector.items():out|=value<<(width*term_id(t))
        return out
    all_pivots={}
    for roots in permutations(order,3):
        if any(not later[v] and v not in roots for v in order):continue
        layer=[(coefficients,())]
        for v in order:
            nxt=[];pivots={};vb=1<<v
            for w in ((None,) if v in roots else later[v]):
                for vec,path in layer:
                    successor={}
                    for (a,b),value in vec.items():
                        aa=a&~vb;bb=b&~vb
                        if w is None:
                            if a&vb and v!=roots[0] or b&vb and v!=roots[2]:continue
                        else:
                            if a&vb:aa|=1<<w
                            if b&vb:bb|=1<<w
                            if aa&bb:continue
                        add(successor,(aa,bb),value)
                    word=packed(successor)
                    while word:
                        p=word.bit_length()-1
                        if p not in pivots:
                            pivots[p]=word;nxt.append((successor,path+(w,)));break
                        word^=pivots[p]
            layer=nxt
            if not layer:break
        for vec,path in layer:
            if set(vec)!={(0,0)}:raise AssertionError("unabsorbed demands")
            actual=word=vec[0,0]
            while word:
                p=word.bit_length()-1
                if p not in all_pivots:
                    all_pivots[p]=word;break
                word^=all_pivots[p]
            if not word:continue
            labels={}
            for v,w in reversed(list(zip(order,path))):
                labels[v]=roots.index(v) if w is None else labels[w]
            parts=[sum(1<<v for v,i in labels.items() if i==j) for j in range(3)]
            a,b=dual.cut(parts[0]),dual.cut(parts[2])
            check=0
            for (i,j),column in columns.items():
                if (((a>>i)&(b>>j))^((a>>j)&(b>>i)))&1:check^=column
            if check!=actual or not dual.compatible(parts[0],parts[2]):raise AssertionError("bad witness")
            yield a,b,parts
            if len(all_pivots)==width:return

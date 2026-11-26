"""Exact guard counts by a minimum-rank completion of mask-tree anchors."""


def par(value):
    return value.bit_count()%2


def mask_trees(masks):
    edges={}
    for i,u in enumerate(masks):
        v=u^(1<<i)
        edges.setdefault(u,[]).append((v,i))
        edges.setdefault(v,[]).append((u,i))
    trees=[]
    covered=set()
    for r in edges:
        if r in covered:continue
        nodes=[(r,None,None)]
        covered.add(r)
        for u,parent,_ in nodes:
            for v,i in edges[u]:
                if v==parent:continue
                assert v not in covered
                covered.add(v)
                nodes.append((v,u,i))
        trees.append(nodes)
    return trees


def completion(pairs):
    def search(limit, cols, span):
        for x,y in pairs:
            if x not in span and y not in span:
                if not limit:return None
                for z in (x,y):
                    expanded=dict(span)
                    expanded.update({a^z:v|(1<<len(cols)) for a,v in span.items()})
                    found=search(limit-1,cols+[z],expanded)
                    if found is not None:return found
                return None
        return cols,[span[x] if x in span else span[y] for x,y in pairs]
    for limit in range(len(pairs)+1):
        choice=search(limit,[],{0:0})
        if choice is not None:return choice


def convolve(left,right,delta=0):
    result={}
    for p,a in left.items():
        for q,b in right.items():
            v=p^q^delta
            result[v]=result.get(v,0)+a*b
    return result


def count(masks, offset, labels, t):
    trees=mask_trees(masks)
    roots=[tree[0][0] for tree in trees]
    owner={i:j for j,tree in enumerate(trees) for _,_,i in tree[1:]}
    pairs=[]
    for i in range(len(masks)):
        h=sum(((r>>i)&1)<<j for j,r in enumerate(roots))
        pairs.append((h,h^(1<<owner[i])))
    basis,weights=completion(pairs)
    d=len(basis)
    global_counts={}
    for sigma in range(1<<d):
        across={0:1}
        for j,tree in enumerate(trees):
            root=roots[j]
            U=sum(((b>>j)&1)<<k for k,b in enumerate(basis))
            tables={u:[{0:1},{0:1}] for u,_,_ in tree}
            for v,u,i in reversed(tree[1:]):
                wi=weights[i]
                residual=((root>>i)&1)^par(U&wi)
                own=(residual<<(t+d)) | (wi<<t) | labels[i]
                for state in (0,1):
                    subtotal={}
                    for child in (0,1):
                        x=state^child
                        before=state if masks[i]==u else child
                        if x and before!=((offset>>i)&1):continue
                        for p,a in tables[v][child].items():
                            key=p^(own if x else 0)
                            subtotal[key]=subtotal.get(key,0)+a
                    tables[u][state]=convolve(tables[u][state],subtotal)
            local={}
            for state in (0,1):
                for val,k in tables[root][state].items():
                    if (val>>(t+d))!=(state^par(U&sigma)):continue
                    lower=val&((1<<(t+d))-1)
                    local[lower]=local.get(lower,0)+k
            across=convolve(across,local)
        for val,k in across.items():
            if val>>t==sigma:
                p=val&((1<<t)-1)
                global_counts[p]=global_counts.get(p,0)+k
    return d,global_counts

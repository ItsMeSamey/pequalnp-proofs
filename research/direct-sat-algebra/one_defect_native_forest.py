"""Count original single-mark supports by Fourier filtering signed tree partitions."""
from itertools import combinations,product
from quadratic_target import affine_domain,apply_basis,insert,parity,reduce_vector


def count(rows,beta,pivot=None,*,layout_cap=729):
    n=len(rows)
    if layout_cap<0 or any(v<0 or v>=1<<n for v in (*rows,beta)):
        raise ValueError("invalid input")
    if not beta:
        return 0,None,{}
    if pivot is None:
        pivot=(beta&-beta).bit_length()-1
    if not 0<=pivot<n or not beta>>pivot&1:
        raise ValueError("invalid pivot")
    d=n-1
    origin=1<<pivot
    dirs=[(1<<i)^(((beta>>i)&1)<<pivot) for i in range(n) if i!=pivot]
    def eq(v):
        return sum(parity(v&x)<<i for i,x in enumerate(dirs)),1^parity(v&origin)
    lines=set()
    planes=set()
    physical=[]
    for i,r in enumerate(rows):
        f=[eq(1<<i),eq(r)]
        if affine_domain(d,f) is None:
            continue
        form={v:c for v,c in f if v}
        if not form:
            return 0,None,{}
        if len(form)==1:
            lines.update(form)
        else:
            (a,x),(b,y)=form.items()
            form[a^b]=x^y
            planes.add(tuple(sorted(form)))
        physical.append(form)
    B=set(lines)
    choices=[]
    for P in sorted(planes):
        opts=list(combinations(P,2))
        B.update(min(opts,key=lambda pair:len(set(pair)-B)))
        choices.append(opts)
    if 3**len(planes)<=layout_cap:
        for pick in product(*choices):
            trial=lines.union(*pick)
            if len(trial)<len(B):
                B=trial
    B=sorted(B)
    N=len(B)
    basis={}
    checks=[]
    for i,v in enumerate(B):
        r,c=reduce_vector(v,basis)
        if r:
            insert(v,1<<i,basis)
        else:
            checks.append(c^(1<<i))
    h=len(checks)
    # Each input row contributes at most one edge, including repeated edges.
    allowed=[{0,1} for _ in B]
    graph=[[] for _ in B]
    edges=[]
    for form in physical:
        lits=[(i,form[v]) for i,v in enumerate(B) if v in form][:2]
        if len(lits)==1:
            i,a=lits[0]
            allowed[i].discard(a)
        else:
            (i,a),(j,b)=lits
            graph[i].append((j,len(edges),a,b))
            graph[j].append((i,len(edges),b,a))
            edges.append((i,j,a,b))
    components=[]
    seen=set()
    for i in range(N):
        if i in seen:
            continue
        seen.add(i)
        todo=[i]
        children={i:[]}
        tree=set()
        incident=set()
        for j in todo:
            for k,e,a,b in graph[j]:
                incident.add(e)
                if k not in seen:
                    seen.add(k)
                    todo.append(k)
                    children[k]=[]
                    children[j].append((k,a,b))
                    tree.add(e)
        extra=[edges[e] for e in sorted(incident-tree)]
        assert len(extra)<=2
        # Conditioning one endpoint per surplus edge suffices.
        anchors=sorted({u for u,_,_,_ in extra})
        components.append((todo,children,extra,anchors))
    def filtered(pins):
        total=0
        for char in range(1<<h):
            negative=apply_basis(checks,char)
            val=1
            for order,children,extra,anchors in components:
                subtotal=0
                for assignment in range(1<<len(anchors)):
                    fixed={u:assignment>>j&1 for j,u in enumerate(anchors)}
                    bans={(v,b) for u,v,a,b in extra if fixed[u]==a}
                    table={}
                    for u in reversed(order):
                        column=[]
                        for a in (0,1):
                            w=int(a in allowed[u] and pins.get(u,a)==fixed.get(u,a)==a and (u,a) not in bans)
                            if a and negative>>u&1:
                                w=-w
                            for v,x,y in children[u]:
                                w*=sum(table[v][b] for b in (0,1) if (a,b)!=(x,y))
                            column.append(w)
                        table[u]=column
                    subtotal+=sum(table[order[0]])
                val*=subtotal
            total+=val
        result,rem=divmod(total,1<<h)
        assert not rem and result>=0
        return result
    ways=filtered({})
    stats=dict(h=h,cycles=[len(e) for _,_,e,_ in components],free=d-len(basis))
    if not ways:
        return 0,None,stats
    pins={}
    for i in range(N):
        pins[i]=0
        if not filtered(pins):
            pins[i]=1
    y=affine_domain(d,[(v,pins[i]) for i,v in enumerate(B)])[0]
    z=origin^apply_basis(dirs,y)
    return ways<<stats['free'],z,stats

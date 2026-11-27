"""Native support counts through component-local coordinates and shared binary drift."""
from itertools import combinations,product
from quadratic_target import affine_domain,apply_basis,insert,parity,reduce_vector


def completion(columns,missing,s):
    """Return completed columns of rank <=s; missing[j] lists erased row bits."""
    k=len(columns)
    for t in range(min(s,k)+1):
        for J in combinations(range(k),t):
            variants=[]
            for j in J:
                bits=[i for i in range(missing[j].bit_length()) if missing[j]>>i&1]
                variants.append([columns[j]^apply_basis([1<<i for i in bits],a) for a in range(1<<len(bits))])
            for piv in product(*variants):
                basis={}
                if any(not insert(v,0,basis) for v in piv):
                    continue
                full=[]
                for c,m in zip(columns,missing):
                    projected={}
                    for i,v in enumerate(piv):
                        insert(v&~m,1<<i,projected)
                    r,a=reduce_vector(c,projected)
                    if r:
                        break
                    full.append(apply_basis(piv,a))
                else:
                    return full
    return None


def compile_rows(rows,beta,pivot):
    """Each local form is (formal vertex mask, original physical coordinate mask)."""
    n=len(rows)
    physical=[i for i in range(n) if i!=pivot]
    x=[sum((((1<<i if i!=pivot else beta)&(1<<j))!=0)<<k for k,j in enumerate(physical)) for i in range(n)]
    def eq(v):
        return apply_basis(x,v),1^(v>>pivot&1)
    clauses=[]
    lines=set()
    planes=set()
    for i,r in enumerate(rows):
        f=[eq(1<<i),eq(r)]
        if affine_domain(n-1,f) is None:
            continue
        form={a:b for a,b in f if a}
        if not form:
            return None
        if len(form)==1:
            lines.update(form)
        else:
            (a,c),(b,d)=form.items()
            form[a^b]=c^d
            planes.add(tuple(sorted(form)))
        clauses.append((i,form))
    B=set(lines)
    for P in sorted(planes):
        B.update(min(combinations(P,2),key=lambda p:len(set(p)-B)))
    B=sorted(B)
    links=[set() for _ in B]
    raw=[]
    for i,form in clauses:
        edge=[(j,form[v]) for j,v in enumerate(B) if v in form][:2]
        if len(edge)==2:
            a,b=[j for j,_ in edge]
            links[a].add(b)
            links[b].add(a)
        raw.append((i,edge))
    seen=set()
    parts=[]
    for first in range(len(B)):
        if first in seen:
            continue
        C=[first]
        seen.add(first)
        for a in C:
            for b in sorted(links[a]-seen):
                seen.add(b)
                C.append(b)
        vertices=[B[j] for j in C]
        loc={a:j for j,a in enumerate(C)}
        owners={}
        gates=[]
        for i,edge in raw:
            if edge[0][0] not in loc:
                continue
            edge=[(loc[j],c) for j,c in edge]
            masks=[1<<j for j,c in edge]
            rep=next(t for t in range(1<<len(masks)) if apply_basis(vertices,apply_basis(masks,t))==x[i])
            owners[i]=apply_basis(masks,rep)
            gates.append(edge)
        abstract={}
        for v in owners.values():
            insert(v,0,abstract)
        extra=[]
        for j,v in enumerate(vertices):
            if insert(1<<j,0,abstract):
                extra.append((1<<j,apply_basis([1<<i for i in physical],v)))
        assert len(extra)<=2
        parts.append((len(C),owners,gates,extra))
    return parts


def local_partition(N,gates,linear,pairpins):
    """Signed tree partition after pinning one endpoint per surplus edge."""
    graph=[[] for _ in range(N)]
    allowed=[{0,1} for _ in range(N)]
    edges=[]
    for edge in gates:
        if len(edge)==1:
            i,a=edge[0]
            allowed[i].discard(a)
        else:
            (i,a),(j,b)=edge
            graph[i].append((j,a,b,len(edges)))
            graph[j].append((i,b,a,len(edges)))
            edges.append((i,a,j,b))
    order=[0]
    children={0:[]}
    tree=set()
    for i in order:
        for j,a,b,e in graph[i]:
            if j not in children:
                order.append(j)
                tree.add(e)
                children[j]=[]
                children[i].append((j,a,b))
    extra=[v for j,v in enumerate(edges) if j not in tree]
    anchors=sorted({i for i,a,j,b in extra})
    assert len(extra)<=2
    total=0
    def compatible(i,a,j,b):
        return all((a^b)==want for want in pairpins.get(tuple(sorted((i,j))),()))
    for w in range(1<<len(anchors)):
        fixed={i:w>>j&1 for j,i in enumerate(anchors)}
        bans={(j,b) for i,a,j,b in extra if fixed[i]==a}
        for i,a,j,b in extra:
            bans.update((j,u) for u in (0,1) if not compatible(i,fixed[i],j,u))
        table={}
        for i in reversed(order):
            row=[]
            for a in (0,1):
                v=(-1 if a and linear>>i&1 else 1) if a in allowed[i] and fixed.get(i,a)==a and (i,a) not in bans else 0
                for j,b,c in children[i]:
                    v*=sum(table[j][u] for u in (0,1) if (a,u)!=(b,c) and compatible(i,a,j,u))
                row.append(v)
            table[i]=row
        total+=sum(table[0])
    return total


def count(rows,beta,s,*,pivot=None,pins=()):
    """Return exact original count, or None if the completion budget fails."""
    n=len(rows)
    if s<0 or any(v<0 or v>=1<<n for v in (*rows,beta)):
        raise ValueError("invalid input")
    if not beta:
        return 0
    if pivot is None:
        pivot=(beta&-beta).bit_length()-1
    if not 0<=pivot<n or not beta>>pivot&1:
        raise ValueError("invalid pivot")
    parts=compile_rows(rows,beta,pivot)
    if parts is None:
        return 0
    drifts=[]
    for _,owners,_,extra in parts:
        local=sum(1<<i for i in owners)
        drifts.extend((v,local) for _,v in extra)
    misses=[sum(((local>>i)&1)<<j for j,(_,local) in enumerate(drifts)) for i in range(n)]
    cols=[sum(((v>>i)&1)<<j for j,(v,_) in enumerate(drifts))&~misses[i] for i in range(n)]
    assert all(m.bit_count()<=2 for m in misses)
    completed=completion(cols,misses,s)
    if completed is None:
        return None
    signals=[]
    basis={}
    localrows=[]
    for j in range(len(drifts)):
        v=sum(((c>>j)&1)<<i for i,c in enumerate(completed))
        if insert(v,1<<len(signals),basis):
            signals.append(v)
        localrows.append((drifts[j][0]^v,reduce_vector(v,basis)[1]))
    used=set().union(*(set(o) for _,o,_,_ in parts))
    pinmap=dict(pins)
    total=0
    for signal in range(1<<len(signals)):
        for char in range(1<<(1+len(signals))):
            phys=apply_basis([beta]+signals,char)
            value=(-1)**parity(char&(1|(signal<<1)))
            for i in set(range(n))-used:
                value*=sum((-1)**(a*(phys>>i&1)) for a in (0,1) if pinmap.get(i,a)==a)
            idx=0
            for N,owners,gates,extra in parts:
                def translate(mask):
                    value=0
                    for i,v in owners.items():
                        if mask>>i&1:
                            value^=v
                    return value
                linear=translate(phys)
                factor=(-1)**int(pivot in owners and phys>>pivot&1)
                restrictions=[]
                for vertex,_ in extra:
                    local,coeff=localrows[idx]
                    idx+=1
                    restrictions.append((vertex^translate(local),parity(coeff&signal)^(local>>pivot&1)))
                # Physical pin masks have at most two active coordinates in a gate edge.
                localg=list(gates)
                pairpins={}
                for i,mask in owners.items():
                    if i not in pinmap:
                        continue
                    nodes=[j for j in range(N) if mask>>j&1]
                    if not nodes:
                        factor*=int(pinmap[i]==int(i==pivot))
                        continue
                    want=pinmap[i]^int(i==pivot)
                    if len(nodes)==1:
                        localg.append([(nodes[0],1^want)])
                    else:
                        pairpins.setdefault(tuple(nodes),[]).append(want)
                signed=0
                for ch in range(1<<len(restrictions)):
                    L=linear; bit=0
                    for j,(mask,a) in enumerate(restrictions):
                        if ch>>j&1:
                            L^=mask; bit^=a
                    signed+=(-1)**bit*local_partition(N,localg,L,pairpins)
                factor*=signed//(1<<len(restrictions))
                value*=factor
            total+=value
    total,rem=divmod(total,1<<(1+len(signals)))
    assert not rem and total>=0
    return total

def search(rows,beta,s,*,pivot=None):
    ways=count(rows,beta,s,pivot=pivot)
    if not ways:
        return ways,None
    pins=[]
    for i in range(len(rows)):
        ways_zero=count(rows,beta,s,pivot=pivot,pins=pins+[(i,0)])
        pins.append((i,int(ways_zero==0)))
    return ways,sum(a<<i for i,a in pins)

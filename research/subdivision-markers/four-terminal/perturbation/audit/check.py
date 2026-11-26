"""Full kernel and routing checks on small multigraphs with named edge IDs."""
from itertools import product
from random import Random


def subsets(s):
    x=s
    while True:
        yield x
        if not x:
            break
        x=(x-1)&s


def xor(cols,s):
    v=0
    while s:
        bit=s&-s
        v^=cols[bit.bit_length()-1]
        s^=bit
    return v


def ids(s):
    return [i for i in range(s.bit_length()) if s>>i&1]


def partition(edges,S,named):
    incidence={}
    for i in ids(S):
        for v in edges[i]:
            incidence.setdefault(v,[]).append(i)
    if set(named)-incidence.keys() or any(len(E)!=2 for v,E in incidence.items() if v not in named):
        return None
    rest=set(ids(S))
    chains=[]
    for start in sorted(named):
        for e in incidence[start]:
            if e not in rest:
                continue
            u=start
            path=0
            while True:
                rest.remove(e)
                path|=1<<e
                a,b=edges[e]
                u^=a^b
                if u in named:
                    break
                e,=set(incidence[u]) & rest
            chains.append((start,u,path))
    return None if rest else chains


def names(edges,S,D,roots):
    incidence={}
    for e in ids(S):
        for v in edges[e]:
            incidence.setdefault(v,[]).append(e)
    named={v for v,E in incidence.items() if len(E)!=2 or v in D}
    for e in ids(roots):
        named.update(edges[e])
    todo=set(incidence)
    while todo:
        root=next(iter(todo))
        comp,stack={root},[root]
        while stack:
            u=stack.pop()
            for e in incidence[u]:
                a,b=edges[e]
                v=u^a^b
                if v not in comp:
                    comp.add(v)
                    stack.append(v)
        if comp.isdisjoint(named):
            named.add(min(comp))
        todo-=comp
    return named


def signature(chains,weights,roots):
    if chains is None:
        return None
    result=[]
    for a,b,s in chains:
        if s&roots and s&(s-1):
            return None
        result.append((min(a,b),max(a,b),xor(weights,s),s&roots))
    return tuple(sorted(result))


def route_options(edges,named,D,weights,segment):
    a,b,w,root=segment
    allowed=set(v for e in edges for v in e)-named-D
    for i,(u,v) in enumerate(edges):
        if {u,v}=={a,b} and w==weights[i] and (not root or root==1<<i):
            yield 1<<i,set()
    if root:
        return
    for i,(u,v) in enumerate(edges):
        if a not in (u,v):
            continue
        c=a^u^v
        if c not in allowed:
            continue
        for j,(x,y) in enumerate(edges):
            if i==j or b not in (x,y):
                continue
            d=b^x^y
            if d not in allowed:
                continue
            initial=(1<<i)|(1<<j)
            gain=w^weights[i]^weights[j]
            if c==d:
                if not gain:
                    yield initial,{c}
                continue
            # Independent brute-force middle linkage oracle for this branch.
            def paths(q,seen,chosen,target):
                if q==d:
                    if not target:
                        yield chosen,seen
                    return
                for e,(t,z) in enumerate(edges):
                    if q in (t,z):
                        nxt=q^t^z
                        if nxt in allowed and nxt not in seen:
                            yield from paths(nxt,seen|{nxt},chosen|(1<<e),target^weights[e])
            yield from paths(c,{c},initial,gain)


def run():
    rng=Random(937502)
    cases=routes=circuits=0
    shapes={'root-loop':0,'unrooted-pure':0,'digon':0,'rooted-pure':0}
    for trial in range(240):
        n=rng.randrange(2,6)
        m=rng.randrange(1,8)
        edges=[tuple(rng.choices(range(n),k=2)) for _ in range(m)]
        k,h,label=(rng.randrange(3) for _ in range(3))
        U=[rng.getrandbits(n) for _ in range(k)]
        D={v for v in range(n) if any(u>>v&1 for u in U)}
        weights=[rng.getrandbits(k+h+label) for _ in edges]
        A=[(1<<a)^(1<<b)^xor(U,w&((1<<k)-1))^(((w>>k)&((1<<h)-1))<<n)
           for (a,b),w in zip(edges,weights)]
        roots=rng.getrandbits(m)&rng.getrandbits(m)
        for S in range(1,1<<m):
            if roots&~S:
                continue
            named=names(edges,S,D,roots)
            parts=partition(edges,S,named)
            assert parts
            sig=signature(parts,weights,roots)
            assert sig is not None
            whole={s for s in subsets(S) if not xor(A,s)}
            small=[((1<<a)^(1<<b)^xor(U,xor(weights,e)&((1<<k)-1))^
                    (((xor(weights,e)>>k)&((1<<h)-1))<<n)) for a,b,e in parts]
            expanded={xor([e for _,_,e in parts],s) for s in range(1<<len(parts)) if not xor(small,s)}
            assert whole==expanded
            circuits+=whole=={0,S}
            cases+=1
            degree={}
            for i in ids(S):
                for v in edges[i]:
                    degree[v]=degree.get(v,0)+1
            shapes['rooted-pure']+=bool(roots) and all(d==2 for d in degree.values())
            for a,b,e in parts:
                if a!=b:
                    continue
                shapes['root-loop']+=bool(e&roots)
                shapes['digon']+=e.bit_count()==2
                shapes['unrooted-pure']+=not bool(e&roots) and len(parts)==1
            if trial<180 and (rng.randrange(12)==0 or S==roots):
                examined=set()
                for options in product(*(route_options(edges,named,D,weights,t) for t in sig)):
                    used,inside=0,set()
                    for e,vertices in options:
                        if used&e or inside&vertices:
                            break
                        used|=e
                        inside|=vertices
                    else:
                        if not roots&~used:
                            examined.add(used)
                brute=set()
                for s in range(1,1<<m):
                    if roots&~s or any((a in D-named or b in D-named) for i,(a,b) in enumerate(edges) if s>>i&1):
                        continue
                    if signature(partition(edges,s,named),weights,roots)==sig:
                        brute.add(s)
                assert examined==brute
                routes+=1
    print(cases,'exact kernel spaces;',circuits,'circuits;',routes,'template routing tables;',shapes)


if __name__=='__main__':
    run()

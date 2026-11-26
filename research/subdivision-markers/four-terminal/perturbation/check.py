"""Exhaust actual and chain-compressed kernels of graph incidence perturbations."""
from itertools import combinations
from random import Random


def xsum(vals):
    r=0
    for x in vals:
        r^=x
    return r


def rank(vals):
    piv={}
    for x in vals:
        while x:
            i=x.bit_length()-1
            if i not in piv:
                piv[i]=x
                break
            x^=piv[i]
    return len(piv)


def compress(n,edges,weights,U,sel,roots):
    inc=[[] for _ in range(n)]
    for i,(a,b) in enumerate(edges):
        if sel>>i&1:
            inc[a].append(i)
            inc[b].append(i)
    mark={i for i,ls in enumerate(inc) if len(ls)!=2 or any((u>>i)&1 for u in U)}
    for i,(a,b) in enumerate(edges):
        if (roots>>i)&1:
            mark.update((a,b))
    seen=set()
    paths=[]
    for v in list(mark)+list(range(n)):
        for i in inc[v]:
            if i in seen:
                continue
            end=v
            e=i
            path=[]
            while True:
                seen.add(e)
                path.append(e)
                a,b=edges[e]
                end^=a^b
                if end in mark or end==v:
                    break
                e=next(j for j in inc[end] if j!=e)
            paths.append((path,(1<<v)^(1<<end)))
    cols=[]
    for segment,boundary in paths:
        z=xsum(weights[i] for i in segment)
        cols.append(boundary^xsum(u for j,u in enumerate(U) if z>>j&1))
    return paths,cols


if __name__=='__main__':
    rng=Random(61295)
    checked=circuits=0
    for _ in range(100):
        n=rng.randint(3,8)
        edges=list(combinations(range(n),2))
        rng.shuffle(edges)
        edges=edges[:rng.randint(1,min(9,len(edges)))]
        k=rng.randrange(4)
        d=rng.randrange(n+1)
        allowed=rng.sample(range(n),d)
        U=[sum(rng.randrange(2)<<i for i in allowed) for _ in range(k)]
        w=[rng.randrange(1<<k) for _ in edges]
        B=[(1<<a)^(1<<b) for a,b in edges]
        A=[b^xsum(u for h,u in enumerate(U) if (z>>h)&1) for b,z in zip(B,w)]
        roots=1<<rng.randrange(len(edges))
        for s in range(1<<len(edges)):
            if s&roots!=roots:
                continue
            paths,cols=compress(n,edges,w,U,s,roots)
            selected=[a for i,a in enumerate(A) if s>>i&1]
            assert len(selected)-rank(selected)==len(cols)-rank(cols)
            assert xsum(selected)==xsum(cols)
            if len(selected)-rank(selected)==1 and not xsum(selected):
                assert len(selected)-rank(b for i,b in enumerate(B) if s>>i&1)<=k+1
                circuits+=1
            checked+=1
    print(checked,'support kernels;',circuits,'circuits checked')

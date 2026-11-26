"""Compare transported binary clauses against independently enumerated row lines."""
from itertools import product
from random import Random


def act(A,x):
    return (A[0] if x&1 else 0) ^ (A[1] if x&2 else 0)


def brute(blocks,full):
    r=len(blocks[0])
    for lines in product((1,2,3),repeat=r):
        if all(any(all(i in full or act(A,v) in (0,lines[i]) for i,A in enumerate(col))
                   for v in (1,2,3)) for col in blocks):
            return True
    return False


def test(blocks,full):
    r=len(blocks[0]); n=r+len(blocks)
    edges=[[] for _ in range(n)]; rankone=[]
    for e,col in enumerate(blocks):
        for i,A in enumerate(col):
            if i in full:continue
            p=tuple(act(A,x) for x in range(4))
            if len(set(p))==4:
                edges[r+e].append((i,p))
                edges[i].append((r+e,tuple(p.index(j) for j in range(4))))
            elif len(set(p))==2:
                rankone.append((r+e,next(j for j in (1,2,3) if not p[j]),i,max(p)))
    roots={}; frames={}; domains={}
    for i in range(n):
        if i in roots:continue
        roots[i]=i; frames[i]=tuple(range(4)); stack=[i]; good={1,2,3}
        while stack:
            t=stack.pop()
            for u,p in edges[t]:
                f=tuple(p[j] for j in frames[t])
                if u not in roots:
                    roots[u]=i; frames[u]=f; stack.append(u)
                else:
                    good={j for j in good if f[j]==frames[u][j]}
        if not good:return False
        domains[i]=good
    atom={(i,t):j+1 for j,(i,t) in enumerate(product(domains,(1,2,3)))}
    clauses=[]
    for i,allowed in domains.items():
        for u,v in ((1,2),(2,3),(1,3)):
            clauses.append((-atom[i,u],-atom[i,v]))
        for u in {1,2,3}-allowed:
            clauses.append((-atom[i,u],-atom[i,u]))
    for u,a,v,b in rankone:
        clauses.append((atom[roots[u],frames[u].index(a)],atom[roots[v],frames[v].index(b)]))
    imp={s*k:set() for k in atom.values() for s in (-1,1)}
    for u,v in clauses:imp[-u].add(v); imp[-v].add(u)
    def reach(u):
        seen={u}; stack=[u]
        while stack:
            t=stack.pop()
            for v in imp[t]-seen:seen.add(v); stack.append(v)
        return seen
    return all(-k not in reach(k) or k not in reach(-k) for k in atom.values())


if __name__=='__main__':
    rng=Random(8382)
    for _ in range(1200):
        r=rng.randrange(1,5); blocks=[]
        for e in range(rng.randrange(1,8)):
            while True:
                col=[(rng.randrange(4),rng.randrange(4)) for i in range(r)]
                if all(any(act(A,x) for A in col) for x in (1,2,3)):break
            blocks.append(col)
        full={i for i in range(r) if rng.randrange(4)==0}
        assert brute(blocks,full)==test(blocks,full)
    print('1200 mixed-rank / row-deletion layer instances matched exhaustive search')

"""Structural witness solvers on the original normalized CNF."""
from itertools import combinations
from complete import from_cnf,solve

def two(n,clauses):
    g=[[] for _ in range(2*n)]
    rev=[[] for _ in g]
    def idx(l): return 2*(abs(l)-1)+int(l<0)
    for c in clauses:
        if not c: return None
        a,b=idx(c[0]),idx(c[-1])
        for u,v in [(a^1,b),(b^1,a)]:
            g[u].append(v)
            rev[v].append(u)
    seen=set()
    order=[]
    for s in range(2*n):
        if s in seen: continue
        stack=[(s,False)]
        while stack:
            u,ex=stack.pop()
            if ex: order.append(u); continue
            if u in seen: continue
            seen.add(u)
            stack.append((u,True))
            stack.extend((v,False) for v in g[u] if v not in seen)
    comp={}
    for i,s in enumerate(reversed(order)):
        if s in comp: continue
        comp[s]=i
        stack=[s]
        while stack:
            u=stack.pop()
            for v in rev[u]:
                if v not in comp:
                    comp[v]=i
                    stack.append(v)
    if any(comp[2*i]==comp[2*i+1] for i in range(n)): return None
    return sum((comp[2*i]>comp[2*i+1])<<i for i in range(n))

def width_order(n,clauses,k):
    adj=[set() for _ in range(n)]
    for c in clauses:
        for a,b in combinations([abs(x)-1 for x in c],2):
            adj[a].add(b); adj[b].add(a)
    live=set(range(n)); order=[]
    while live:
        v=min(live,key=lambda i:(len(adj[i]),i))
        bag=adj[v]
        if len(bag)>k: return None
        for u in bag:
            adj[u].update(bag-{u})
            adj[u].remove(v)
        live.remove(v)
        order.append((v,tuple(sorted(bag))))
    return order

def tables(clauses,order):
    factors=[]
    for c in clauses:
        vs=tuple(abs(l)-1 for l in c)
        bad=sum((l<0)<<i for i,l in enumerate(c))
        factors.append((vs,set(range(1<<len(vs)))-{bad}))
    choices=[]
    for v,bag in order:
        local=[f for f in factors if v in f[0]]
        factors=[f for f in factors if v not in f[0]]
        ix={b:j+1 for j,b in enumerate(bag)}
        ix[v]=0
        chosen={}
        for b in range(1<<len(bag)):
            for bit in (0,1):
                word=2*b+bit
                if all(sum(((word>>ix[u])&1)<<j for j,u in enumerate(scope)) in rows
                       for scope,rows in local):
                    chosen[b]=bit
                    break
        choices.append((v,bag,chosen))
        if not chosen: return None
        factors.append((bag,set(chosen)))
    if any(not r for _,r in factors): return None
    word=0
    for v,bag,c in reversed(choices):
        b=sum(((word>>u)&1)<<j for j,u in enumerate(bag))
        word|=c[b]<<v
    return word

def cover_triples(sets,k):
    if not sets: return ()
    if not k: return None
    for v in sets[0]:
        tail=cover_triples([s for s in sets if v not in s],k-1)
        if tail is not None: return (v,)+tail
    return None

def backdoor_two(n,clauses,variables):
    for assignment in range(1<<len(variables)):
        pinned={v:bool(assignment>>i&1) for i,v in enumerate(variables)}
        residual=[]
        for c in clauses:
            if any(abs(l) in pinned and pinned[abs(l)]==(l>0) for l in c):
                continue
            residual.append(tuple(l for l in c if abs(l) not in pinned))
        w=two(n,residual)
        if w is not None:
            for v,b in pinned.items():
                w=(w&~(1<<(v-1)))|(int(b)<<(v-1))
            return w
    return None

def solve_cnf(n,clauses,*,width=4,backdoor=2,**budgets):
    if n<0 or min(width,backdoor)<0: raise ValueError('negative dimension')
    clauses=[tuple(c) for c in clauses]
    for c in clauses:
        if len(c)>3 or any(not l or abs(l)>n for l in c): raise ValueError('invalid 3CNF')
    clean=[tuple(dict.fromkeys(c)) for c in clauses if all(-l not in c for l in c)]
    if all(len(c)<=2 for c in clean):
        w,route=two(n,clean),'2SAT'
    else:
        order=width_order(n,clean,width)
        if order is not None:
            w,route=tables(clean,order),'width tables'
        else:
            cut=cover_triples([tuple(abs(l) for l in c) for c in clean if len(c)==3],backdoor)
            if cut is not None:
                w,route=backdoor_two(n,clean,cut),'2SAT backdoor'
            else:
                g,out=from_cnf(n,clean)
                w,route=solve(n,g,out,**budgets)
    if w is not None:
        assert all(any(bool(w>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
    return w,route

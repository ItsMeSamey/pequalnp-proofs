"""Canonical affine equations on free variables after fixing both roots."""
from functools import lru_cache
from itertools import combinations


def add(basis,p):
    while p and p.bit_length() in basis:
        p ^= basis[p.bit_length()]
    if p:
        basis[p.bit_length()]=p
    return p


def normalize(adj):
    n=len(adj)
    fixed={}
    for i in (0,1):
        # x_i=1 implies parity of its neighbors is zero.
        add(fixed,((adj[i]>>2)<<1)|((adj[i]&3).bit_count()%2))
    if 1 in fixed:
        return None
    forms=[1,1]
    free_vertices=[]
    for i in range(2,n):
        if i in fixed:
            eq=fixed[i]
            a=eq&1
            for j in range(2,i):
                if eq>>(j-1)&1:
                    a ^= forms[j]
        else:
            a=2<<len(free_vertices)
            free_vertices.append(i)
        forms.append(a)
    return forms,free_vertices


@lru_cache(None)
def ring(free,d):
    mons=[sum(1<<j for j in t) for k in range(d+1) for t in combinations(range(free),k)]
    pos={v:i for i,v in enumerate(mons)}
    low=sum(v.bit_count()<d for v in mons)
    products=[[1<<pos[m|(1<<j)] for m in mons[:low]] for j in range(free)]
    return pos,low,products


def restrictions(adj,forms):
    guards=[]
    for i,neighbors in enumerate(adj):
        rhs=0
        for j,expr in enumerate(forms):
            if neighbors>>j&1:
                rhs ^= expr
        guards.append((forms[i],rhs))
    return guards


def pc(guards,free,d,rounds=None):
    pos,low,products=ring(free,d)
    def bits(u):
        while u:
            b=u&-u
            yield b
            u ^= b
    todo=[]
    for a,b in guards:
        p=0
        for l in bits(a):
            for r in bits(b):
                p ^= 1<<pos[(l|r)>>1]
        todo.append(p)
    basis={}
    for p in todo:
        add(basis,p)
    todo=[p for p in basis.values() if p.bit_length()<=low]
    step=0
    while todo and (rounds is None or step<rounds):
        following=[]
        for p in todo:
            indices=[b.bit_length()-1 for b in bits(p)]
            for images in products:
                q=0
                for j in indices:
                    q ^= images[j]
                q=add(basis,q)
                if q and q.bit_length()<=low:
                    following.append(q)
        todo=following
        step+=1
    if 1 in basis:
        return {j+1:1<<j for j in range(free+1)}
    return {j:p for j,p in basis.items() if j<=free+1}


def exact(guards,free):
    points={}
    for u in range(1,1<<(free+1),2):
        if all(not((a&u).bit_count()%2 and (b&u).bit_count()%2) for a,b in guards):
            add(points,u)
    return free+1-len(points)


def evaluate(adj):
    normalized=normalize(adj)
    if normalized is None:
        return None
    forms,vertices=normalized
    guards=restrictions(adj,forms)
    truth=exact(guards,len(vertices))
    p2=pc(guards,len(vertices),2)
    if len(p2)==truth:
        return truth,truth,truth
    return truth,len(p2),len(pc(guards,len(vertices),3))

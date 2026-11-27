"""Witness lifting on assembled bag instances against direct induced-subgraph search."""
from itertools import combinations
from random import Random
from collections import deque, Counter

def vertices(mask):
    while mask:
        bit=mask & -mask
        yield bit.bit_length()-1
        mask ^= bit

def path(graph, starts, targets, forbidden=0):
    queue=deque(vertices(starts))
    pred={u:None for u in queue}
    while queue:
        v=queue.popleft()
        if (1<<v)&targets:
            result=0
            while v is not None:
                result |= 1<<v
                v=pred[v]
            return result
        for u in vertices(graph[v]&~forbidden):
            if u not in pred:
                pred[u]=v
                queue.append(u)
    return None

def shore_witnesses(g,T,p):
    if p is None:
        return {(0,0):0,(0,1):0,(1,0):T & -T}
    pin=1<<p
    k=int(bool(T&pin))
    ans={(k,0):pin}
    U=T & ~pin
    if not k:
        ans[0,1]=pin
    else:
        w=path(g,pin,U)
        if w is not None:
            ans[0,1]=w
    independent=U & ~g[p]
    if independent:
        ans[1-k,0]=pin | (independent & -independent)
    else:
        w=path(g,U,g[p]&~U,pin)
        if w is not None:
            ans[1-k,0]=w|pin
    return ans

def even(g,s):
    return all((s&g[v]).bit_count()%2==0 for v in vertices(s))

def random_graph(rng,n):
    graph=[0]*n
    for v,w in combinations(range(n),2):
        if rng.randrange(2):
            graph[v] |= 1<<w
            graph[w] |= 1<<v
    return graph

def verify(rng):
    m=rng.randrange(3,7)
    bag=random_graph(rng,m)
    for i in range(1,m):  # ensure a connected representative bag
        bag[i] |= 1<<(i-1)
        bag[i-1] |= 1<<i
    pinbranches=rng.sample(range(m),3)
    g=[]; front=[]; pinmask=0; tables=[]; offsets=[]
    for i in range(m):
        n=rng.randrange(1,4)
        local=random_graph(rng,n)
        T=rng.randrange(1,1<<n)
        p=rng.randrange(n) if i in pinbranches else None
        offset=len(g)
        offsets.append(offset)
        front.append(T<<offset)
        if p is not None: pinmask |= 1<<(offset+p)
        g.extend(adj<<offset for adj in local)
        table=shore_witnesses(local,T,p)
        for (a,b),sel in table.items():
            assert (sel&T).bit_count()%2==a
            assert p is None or (sel>>p)&1
            assert all((sel&local[v]).bit_count()%2==(b if (T>>v)&1 else 0) for v in vertices(sel))
        tables.append(table)
    for i in range(m):
        outside=0
        for j in vertices(bag[i]): outside|=front[j]
        for v in vertices(front[i]): g[v]|=outside
    answer=None
    for a in range(1<<m):
        states=[((a>>i)&1,(a&bag[i]).bit_count()%2) for i in range(m)]
        if all(st in table for st,table in zip(states,tables)):
            answer=sum(tables[i][states[i]]<<offsets[i] for i in range(m))
            break
    optional=((1<<len(g))-1)^pinmask
    rest=optional
    direct=False
    while True:
        if even(g,rest|pinmask):
            direct=True
            break
        if not rest: break
        rest=(rest-1)&optional
    assert (answer is not None)==direct
    if answer is not None:
        assert answer&pinmask==pinmask and even(g,answer)
    return direct

if __name__=="__main__":
    rng=Random(271092)
    print(Counter(verify(rng) for _ in range(700)))

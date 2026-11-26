from itertools import combinations
from collections import deque

def reach(G,start,allowed):
    if start not in allowed: return set()
    seen={start}
    q=deque([start])
    while q:
        for w in G[q.popleft()] & allowed - seen:
            seen.add(w)
            q.append(w)
    return seen

def algorithm(G,s,t,v):
    V=set(range(len(G)))
    H=[set(neighbors) for neighbors in G]
    H[s].remove(t)
    H[t].remove(s)
    if v in (s,t):
        return t in reach(H,s,V)
    if v in G[s] or v in G[t]:
        if v not in G[s]: s,t=t,s
        return v in reach(G,t,V-{s}-(G[s]-{t,v}))
    allowed=V-{v}-G[v]
    S=reach(H,s,allowed)
    if t in S: return True
    T=reach(H,t,allowed)
    for a in G[v]:
        for b in G[v]-{a}-G[a]:
            if a in reach(H,s,(S|{a})-G[b]) and b in reach(H,t,(T|{b})-G[a]):
                return True
    return False

def inspect(n):
    pairs=list(combinations(range(n),2))
    examined=0
    for code in range(1<<len(pairs)):
        G=[set() for _ in range(n)]
        for i,(u,v) in enumerate(pairs):
            if code>>i&1:
                G[u].add(v)
                G[v].add(u)
        if any(len(row)>3 for row in G): continue
        masks=[sum(1<<v for v in row) for row in G]
        models=[x for x in range(1<<n) if all(not(x>>i&1 and (x & masks[i]).bit_count()%2) for i in range(n))]
        for s,t in pairs:
            if t not in G[s]: continue
            rooted=[x for x in models if x>>s&1 and x>>t&1]
            for v in range(n):
                assert algorithm(G,s,t,v)==any(x>>v&1 for x in rooted),(G,s,t,v)
                examined+=1
    return examined

if __name__=='__main__':
    for n in range(2,6): print(n,inspect(n),flush=True)

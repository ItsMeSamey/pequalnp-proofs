"""Compile, then independently trace the exact native gated feedback permutation."""
from itertools import combinations
from random import Random


def compile_network(n,edges,pairs):
    how = {}
    for bit,(e,f) in enumerate(pairs):
        how[e] = bit,0
        how[f] = bit,1
    # Each graph edge gets two half-edge triples with private auxiliary sockets.
    orbits = [[v] for v in range(n+len(edges))]
    track = len(orbits)
    fixed = []
    word = []
    nextbit = len(pairs)
    def triple(u,v,bit,on):
        nonlocal track
        a,b,c = range(track,track+3)
        track += 3
        orbits[u].append(a)
        orbits[v].append(b)
        orbits.append([c])
        if on == 0:
            fixed.append((a,b,c))
        if bit is not None:
            word.append((bit,(a,b,c) if on else (a,c,b)))
    for e,(u,v) in enumerate(edges):
        bit,on = how.get(e,(None,0))
        triple(u,n+e,bit,on)
        triple(n+e,v,nextbit,1)
        nextbit += 1
    perm = list(range(track))
    for cyc in orbits:
        for i,a in enumerate(cyc):
            perm[a] = cyc[(i+1)%len(cyc)]
    for a,b,c in fixed:
        perm[a],perm[b],perm[c] = perm[b],perm[c],perm[a]
    return perm,word,nextbit


def safe(n,edges,pairs):
    forbid={a:b for a,b in pairs}|{b:a for a,b in pairs}
    def walk(u,visited,used):
        if u==n-1:
            return True
        for i,(x,y) in enumerate(edges):
            if u!=x and u!=y:
                continue
            v=x+y-u
            if v not in visited and forbid.get(i) not in used:
                if walk(v,visited|{v},used|{i}):
                    return True
        return False
    return walk(0,{0},set())


def native(n,edges,pairs):
    f,g,m=compile_network(n,edges,pairs)
    assert all(sum(j==i for j,_ in g)<=2 for i in range(m))
    hits=0
    for mask in range(1<<m):
        p=f[:]
        for bit,(a,b,c) in g:
            if mask>>bit&1:
                p[a],p[b],p[c]=p[b],p[c],p[a]
        x=p[0]
        while x!=0 and x!=n-1:
            x=p[x]
        hits += x==n-1
    return bool(hits),1<<m


if __name__=='__main__':
    rng=Random(240)
    total=yes=0
    for case in range(700):
        n=rng.randrange(2,8)
        all_edges=list(combinations(range(n),2))
        edges=[rng.choice(all_edges) for _ in range(rng.randrange(8))]
        ids=rng.sample(range(len(edges)),len(edges))
        count=rng.randrange(1+len(ids)//2)
        pairs=list(zip(ids[:2*count:2],ids[1:2*count:2]))
        found, num=native(n,edges,pairs)
        assert found==safe(n,edges,pairs)
        total+=num
        yes+=found
    print(f'700 multigraphs, {total} physical settings, {yes} positive and {700-yes} negative instances')

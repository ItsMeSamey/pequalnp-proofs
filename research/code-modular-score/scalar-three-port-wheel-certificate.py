from itertools import combinations
def partitions(n):
    def walk(i,p):
        if i==n:
            yield tuple(p)
        else:
            for j in range(len(p)):
                yield from walk(i+1,p[:j]+[p[j]|(1<<i)]+p[j+1:])
            yield from walk(i+1,p+[1<<i])
    return walk(0,[])
def check(n,edges,ports,odd):
    def connected(s):
        t=s&-s
        while True:
            z=t
            for a,b in edges:
                e=1<<a|1<<b
                if e&s==e and t&e:t|=e
            if t==z:return t==s
    connected_sets={s for s in range(1,1<<n) if connected(s)}
    states=set(); contracted=[set() for e in edges]
    for part in partitions(n):
        if not connected_sets.issuperset(part):continue
        hole=any(not any(s>>i&1 for i in ports) and (s&odd).bit_count()%2 for s in part)
        state=tuple(sorted((sum(1<<j for j,i in enumerate(ports) if s>>i&1),0 if hole else (s&odd).bit_count()%2) for s in part if any(s>>i&1 for i in ports))),hole
        states.add(state)
        for i,(a,b) in enumerate(edges):
            if any(s>>a&1 and s>>b&1 for s in part):contracted[i].add(state)
    return states,[states-c for c in contracted]

if __name__ == '__main__':
    ports = (0,1,2)
    odd = (1<<3) | (1<<4)
    edges = [(0,1),(0,4),(0,5),(1,2),(1,5),(2,3),(2,5),(3,4),(3,5),(4,5)]
    states, losses = check(6, edges, ports, odd)
    assert len(states) == 15
    for e,lost in zip(edges,losses,strict=True):
        if not set(e).issubset(ports):
            assert lost
            print(e, sorted(lost)[0])
    for k in range(3):
        for extra in combinations((3,4,5),k):
            support = ports + extra
            reduced_edges = [(support.index(i),support.index(j)) for i,j in edges
                             if i in support and j in support]
            reduced_odd = sum(1<<i for i,v in enumerate(support) if odd>>v&1)
            smaller,_ = check(len(support),reduced_edges,ports,reduced_odd)
            assert states - smaller
    print("All proper vertex supports and port-preserving contractions excluded.")

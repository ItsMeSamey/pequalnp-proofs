from itertools import combinations
for n in range(5):
    possible=list(combinations(range(n),2))
    for graph in range(1<<len(possible)):
        edges=[e for i,e in enumerate(possible) if graph>>i&1]
        k=n+2
        encoded=0
        for x in range(1<<(n+1)):
            uncut=sum(((x>>a)&1)==((x>>b)&1) for u,v in edges for a,b in [(u,v),(u,n),(v,n)])
            encoded+=1<<(k*uncut)
        covers=sum(all((x>>u|x>>v)&1 for u,v in edges) for x in range(1<<n))
        assert (encoded>>(k*len(edges)))% (1<<k) == 2*covers
print('All 76 labeled graphs of sizes zero through four passed.')

from itertools import combinations
def test(n, edges):
    best=0
    for m in range(1<<len(edges)):
        blocks=[]
        for j,e in enumerate(edges):
            if m>>j&1:
                s=set(e)
                disjoint=[b for b in blocks if not b&s]
                s.update(*(b for b in blocks if b&s))
                blocks=disjoint+[s]
        best=max(best,m.bit_count()-sum(map(len,blocks))+len(blocks))
    return best,sum(all(len({(x>>i)&1 for i in e})==2 for e in edges) for x in range(1<<n))
for n,edges in [(4,list(combinations(range(4),3))),(7,[{j,(j+1)%7,(j+3)%7} for j in range(7)]),(9,[[3*x+(a*x+b)%3 for x in range(3)] for a in range(3) for b in range(3)]+[[3*x+j for j in range(3)] for x in range(3)])]:
    print(n,len(edges),test(n,edges))

"""Direct count of ordered edge colorings of small prisms and Petersen lifts."""
def count(n,edges):
    neighbors=[[] for _ in range(n)]
    for e,(u,v) in enumerate(edges):
        neighbors[u].append(e)
        neighbors[v].append(e)
    assert all(len(row)==3 for row in neighbors)
    taken=[0]*n
    pending=set(range(len(edges)))
    def visit():
        if not pending:
            return 1
        e=min(pending,key=lambda edge:(7^(taken[edges[edge][0]]|taken[edges[edge][1]])).bit_count())
        a,b=edges[e]
        allowed=7^(taken[a]|taken[b])
        pending.remove(e)
        result=0
        for color in (1,2,4):
            if allowed&color:
                taken[a]^=color
                taken[b]^=color
                result+=visit()
                taken[a]^=color
                taken[b]^=color
        pending.add(e)
        return result
    return visit()

def lift(edges,switched):
    return [(2*u+j,2*v+(j^int(i in switched))) for i,(u,v) in enumerate(edges) for j in (0,1)]

for n in (3,5,7):
    prism=[(j,(j+1)%n) for j in range(n)]+[(n+j,n+(j+1)%n) for j in range(n)]+[(j,n+j) for j in range(n)]
    val=count(2*n,prism)
    assert val==(1<<n)-2
    print('odd prism',n,val)
petersen=[(j,(j+1)%5) for j in range(5)]+[(5+j,5+(j+2)%5) for j in range(5)]+[(j,5+j) for j in range(5)]
controls=[count(10,petersen),count(20,lift(petersen,range(15))),count(20,lift(petersen,{0}))]
assert controls==[0,192,0]
print('base, all-edge cover, single-edge twist',controls)

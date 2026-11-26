from solver import bits, component


def graph(k):
    adj=[0]*(6*k+3)
    def edge(a,b):
        assert not(adj[a]>>b&1)
        adj[a]|=1<<b
        adj[b]|=1<<a
    A,x,z=0,1,2
    edge(A,x); edge(A,z)
    force=[]
    for i in range(k):
        C,v,B,D,w,y=range(3+6*i,9+6*i)
        for a,b in [(A,w),(x,C),(C,v),(v,B),(B,y),(z,D),(A,v),(v,D)]:
            edge(a,b)
        force.extend([(x,C),(z,D),(C,v),(v,B),(B,y),(A,w)])
        A,x,z=D,w,y
    edge(A,x); edge(A,z)
    return adj,force


for k in range(1,31):
    adj,force=graph(k)
    allv=(1<<len(adj))-1
    assert all(a.bit_count() in (2,4) for a in adj)
    assert sum(a.bit_count()==4 for a in adj)==2*k+1
    for i in range(len(adj)):
        remain=allv^(1<<i)
        assert component(adj,next(bits(remain)),remain)==remain
    selected=7
    for i,j in force:
        assert selected>>i&1 and adj[i]&~selected==1<<j
        selected|=1<<j
    assert selected==allv
    if k<=2:
        assert [x for x in range(allv+1) if x&7==7 and
                all(not ((adj[i]&x).bit_count()%2) for i in bits(x))]==[allv]
print("Verified 30 rigid cells/chains and exhaustively checked the first two.")

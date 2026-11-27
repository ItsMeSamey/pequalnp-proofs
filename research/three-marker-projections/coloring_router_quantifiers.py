"""Build and check the two-quantifier native network of an even degree-four graph."""
from itertools import product

def orient(n,edges):
    adjacent=[[]for _ in range(n)]
    for i,(u,v) in enumerate(edges):
        adjacent[u].append((i,v))
        adjacent[v].append((i,u))
    directed=[None]*len(edges)
    stack=[0]
    while stack:
        v=stack[-1]
        if not adjacent[v]:
            stack.pop()
            continue
        i,u=adjacent[v].pop()
        if directed[i] is None:
            directed[i]=(v,u)
            stack.append(u)
    if None in directed:
        raise ValueError('graph must be connected')
    return directed

def build(n,edges):
    directed=orient(n,edges)
    m=len(edges)
    ins=[[]for _ in range(n)]
    outs=[[]for _ in range(n)]
    for i,(u,v) in enumerate(directed):
        outs[u].append(i)
        ins[v].append(i)
    if any(len(x)!=2 for x in ins+outs):raise ValueError('graph must be 4-regular')
    wiring=[None]*(3*(m+3*n))
    for i,(u,v) in enumerate(directed):
        for j in range(3):
            h=m+3*v+(j+1)%3
            wiring[3*i+j]=3*h+ins[v].index(i)
    for v in range(n):
        for x in range(3):
            h=m+3*v+x
            wiring[3*h+2]=3*h+2
            for j,e in enumerate(outs[v]):wiring[3*h+j]=3*e+x
    assert sorted(wiring)==list(range(len(wiring)))
    return directed,ins,outs,wiring,3*outs[0][0]

def native_join(w,start,word):
    j=start
    while True:
        g,k=divmod(j,3)
        j=w[3*g+(k+word[g])%3]
        if j==start:return False
        if j==start+1:return True

def certificate(network,data):
    edges,ins,outs,w,start=network
    n=len(ins)
    succ=[[]for _ in range(3*n)]
    for e,(u,v) in enumerate(edges):
        for x in range(3):
            y=(x+1+data[e])%3
            succ[3*u+x].append((3*v+y,3*e+x))
    routers=[None]*(3*n)
    connected=False
    for first in range(3*n):
        if not succ[first]:continue
        stack=[(first,None)]
        cycle=[]
        while stack:
            v,enter=stack[-1]
            if succ[v]:stack.append(succ[v].pop())
            else:
                stack.pop()
                if enter is not None:cycle.append(enter)
        cycle.reverse()
        sheets=set()
        for dart,following in zip(cycle,cycle[1:]+cycle[:1]):
            e,x=divmod(dart,3)
            f,y=divmod(following,3)
            v=edges[e][1]
            assert v==edges[f][0] and y==(x+1+data[e])%3
            hub=3*v+y
            sheets.add(hub)
            bit=ins[v].index(e)^outs[v].index(f)
            assert routers[hub] in (None,bit)
            routers[hub]=bit
        if {0,1}<=sheets:connected=True
    assert None not in routers
    assert native_join(w,start,tuple(data)+tuple(routers))==connected
    return connected,routers

def normalized_colorings(n,edges):
    return [c for c in product(range(3),repeat=n) if c[0]==0 and all(c[u]!=c[v] for u,v in edges)]

def check(n,edges,exhaust_routers=False):
    net=build(n,edges)
    expected={tuple((c[v]-c[u])%3-1 for u,v in net[0])for c in normalized_colorings(n,edges)}
    observed=set()
    for data in product((0,1),repeat=len(edges)):
        joined,_=certificate(net,data)
        if not joined:observed.add(data)
        if exhaust_routers:
            answers=[native_join(net[3],net[4],data+r) for r in product((0,1),repeat=3*n)]
            assert any(answers)==joined
    assert observed==expected
    print('vertices',n,'data masks',2**len(edges),'protected masks',len(observed),'complete routers',exhaust_routers)

if __name__=='__main__':
    check(2,[(0,1)]*4,True)
    check(3,[(0,1),(1,2),(2,0)]*2,True)
    check(5,[(i,j) for i in range(5)for j in range(i)])
    check(6,[(i,j) for i in range(6)for j in range(i) if i//2!=j//2])

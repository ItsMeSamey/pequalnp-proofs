"""Count physical perfect matchings and their complementary cycles."""
def necklace(k):
    graph=[set() for _ in range(12*k)]
    def add(a,b):
        assert a!=b and b not in graph[a]
        graph[a].add(b)
        graph[b].add(a)
    ends=[]
    for j in range(2*k):
        edges=[(i,(i+1)%3) for i in range(3)]+[(3+i,3+(i+1)%3) for i in range(3)]
        edges.extend((i,i+3) for i in range(3))
        a,b=(0,3) if j%2==0 else (0,1)
        edges.remove((a,b))
        ends.append((6*j+a,6*j+b))
        for u,v in edges:
            add(6*j+u,6*j+v)
    for j,(a,b) in enumerate(ends):
        add(b,ends[(j+1)%len(ends)][0])
    return graph

def count(graph):
    n=len(graph)
    assert all(len(row)==3 for row in graph)
    def bridgeless(a,b):
        seen={0}
        stack=[0]
        while stack:
            u=stack.pop()
            for v in graph[u]-seen:
                if {u,v}!={a,b}:
                    seen.add(v)
                    stack.append(v)
        return len(seen)==n
    assert all(bridgeless(u,v) for u in range(n) for v in graph[u] if u<v)
    matching={}
    def visit(rem):
        if rem:
            u=min(rem)
            total=good=0
            for v in rem&graph[u]:
                matching[u],matching[v]=v,u
                a,b=visit(rem-{u,v})
                total+=a
                good+=b
            return total,good
        todo=set(range(n))
        while todo:
            start=u=next(iter(todo))
            prev=-1
            length=0
            while True:
                todo.remove(u)
                nxt=next(iter(graph[u]-{matching[u],prev}))
                prev,u=u,nxt
                length+=1
                if u==start:
                    break
            if length%2:
                return 1,0
        return 1,1
    return visit(set(range(n)))

for k in range(1,5):
    result=count(necklace(k))
    assert result==(2**k+6**k,1+4**k)
    print(k,*result)

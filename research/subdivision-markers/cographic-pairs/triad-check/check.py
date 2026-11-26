"""Requires NetworkX; graph vertices 0,...,n-1 and edges labeled by position."""
from itertools import combinations
from random import Random
import networkx as nx


def cuts(n,edges):
    """All root-away shores of 3-edge cuts; assumes 3-edge connectivity."""
    adj=[[] for _ in range(n)]
    for i,(a,b) in enumerate(edges):
        if a==b:raise ValueError("loops must be handled separately")
        adj[a].append((i,b))
        adj[b].append((i,a))
    output={}
    for tri in combinations(range(len(edges)),3):
        removed=set(tri)
        reached={0}
        todo=[0]
        while todo:
            a=todo.pop()
            for i,b in adj[a]:
                if i not in removed and b not in reached:
                    reached.add(b)
                    todo.append(b)
        if len(reached)<n:
            shore=frozenset(set(range(n))-reached)
            actual=tuple(i for i,(a,b) in enumerate(edges) if (a in shore)!=(b in shore))
            if actual!=tri:raise ValueError("graph has a cut smaller than three")
            output[shore]=tri
    return output


def signature_socket(graph,allowed):
    """Return sockets in bit order. No external occupancy means bit zero."""
    if not allowed:return None
    baseline=min(allowed)
    dev={baseline^x for x in allowed}
    if not dev<={0,3,5,6}:raise ValueError("expected even deviations")
    ports=[]
    mates=[]
    for i in range(3):
        p=len(graph);q=p+1
        graph.add_edge(p,q)
        mates.append(q)
        if baseline>>i&1:
            r=len(graph)
            graph.add_edge(p,r)
            p=r
        ports.append(p)
    for i,j in combinations(range(3),2):
        if (1<<i|1<<j) in dev:graph.add_edge(mates[i],mates[j])
    return ports


def solve(n,edges,constraints,pins=None):
    """Return an edge mask or None. Keys of constraints are sorted edge triples."""
    pins={} if pins is None else pins
    shores=cuts(n,edges)
    tri_to_shore={tri:S for S,tri in shores.items()}
    if any(tri not in tri_to_shore for tri in constraints):
        raise ValueError("requested triple is not a three-edge bond")
    root=frozenset(range(n))
    nodes=[tri_to_shore[tri] for tri in constraints]+[root]
    nodes.sort(key=len)
    if any(a&b and not(a<=b or b<=a) for a,b in combinations(nodes,2)):
        raise ValueError("crossing shores")
    children={a:[] for a in nodes}
    for s in nodes:
        if s!=root:children[min((t for t in nodes if s<t),key=len)].append(s)
    tables={}
    for s in nodes:
        tri=shores.get(s,())
        states=constraints[tri] if s!=root else {0}
        children_s=children[s]
        interior={v:("vertex",v) for v in s}
        for c in children_s:
            for v in c:interior[v]=("child",c)
        # Classify original edges by the atoms that own their endpoints.
        sides={}
        incidence={a:[] for a in interior.values()}
        for i,(v,w) in enumerate(edges):
            a,b=interior.get(v),interior.get(w)
            if a==b:continue
            sides[i]=[t for t in (a,b) if t is not None]
            for t in sides[i]:incidence[t].append(i)
        tables[s]={}
        for state in states:
            if state.bit_count()%2:continue
            graph=nx.Graph()
            sockets={i:[] for i in sides}
            valid=True
            for atom,labels in incidence.items():
                kind,v=atom
                if kind=="child":
                    ordered=shores[v]
                    if set(labels)!=set(ordered):raise AssertionError("child boundary")
                    ports=signature_socket(graph,set(tables[v]))
                    if ports is None:
                        valid=False;break
                else:
                    ordered=labels
                    start=len(graph)
                    total=len(labels)+(len(labels)%2)
                    graph.add_nodes_from(range(start,start+total))
                    graph.add_edges_from(combinations(range(start,start+total),2))
                    ports=list(range(start,start+len(labels)))
                for i,p in zip(ordered,ports):sockets[i].append(p)
            if not valid:continue
            chosen=0
            external={}
            for i,ps in sockets.items():
                fixed=pins.get(i)
                if len(ps)==1:
                    required=(state>>tri.index(i))&1
                    if fixed is not None and fixed!=required:
                        valid=False;break
                    fixed=required
                if fixed==1:
                    chosen|=1<<i
                    for p in ps:graph.add_edge(p,len(graph))
                elif fixed is None:
                    a,b=ps
                    graph.add_edge(a,b)
                    external[i]=(a,b)
            if not valid:continue
            mat=nx.max_weight_matching(graph,maxcardinality=True)
            if len(mat)*2!=len(graph):continue
            for i,(a,b) in external.items():
                if (a,b) in mat or (b,a) in mat:chosen|=1<<i
            for c in children_s:
                pattern=sum(((chosen>>i)&1)<<j for j,i in enumerate(shores[c]))
                chosen|=tables[c][pattern]
            tables[s][state]=chosen
    return tables[root].get(0)


def cycle_vectors(n,edges):
    """Independent oracle: fundamental cycles along one spanning tree."""
    tree=[[] for _ in range(n)]
    roots=list(range(n))
    def root(v):
        while roots[v]!=v:v=roots[v]
        return v
    basis=[]
    for i,(a,b) in enumerate(edges):
        if root(a)!=root(b):
            roots[root(a)]=root(b)
            tree[a].append((b,i))
            tree[b].append((a,i))
        else:
            stack=[(a,-1,1<<i)]
            while stack:
                x,p,mask=stack.pop()
                if x==b:
                    basis.append(mask);break
                stack.extend((y,x,mask^(1<<j)) for y,j in tree[x] if y!=p)
    result=[0]
    for c in basis:result += [x^c for x in result]
    return result


def valid(mask,edges,constraints,pins):
    odd=0
    for i,(a,b) in enumerate(edges):
        if mask>>i&1:odd^=1<<a|1<<b
    return not odd and all(
        sum(((mask>>i)&1)<<j for j,i in enumerate(tri)) in allowed
        for tri,allowed in constraints.items()
    ) and all((mask>>i&1)==bit for i,bit in pins.items())


def triangle_expand(n,edges,v):
    original=[e for e in edges if v not in e]
    neighbors=[b if v==a else a for a,b in edges if v in (a,b)]
    replacements=[v,n,n+1]
    return n+2,original+list(zip(neighbors,replacements))+list(combinations(replacements,2))


def main():
    rng=Random(8123)
    ev=(0,3,5,6)
    for mask in range(16):
        allowed={a for j,a in enumerate(ev) if mask>>j&1}
        for x in range(8):
            g=nx.Graph()
            ports=signature_socket(g,allowed)
            ok=ports is not None
            if ok:
                for j,p in enumerate(ports):
                    if x>>j&1:g.add_edge(p,len(g))
                ok=2*len(nx.max_weight_matching(g,maxcardinality=True))==len(g)
            assert ok==(x in allowed)
    graphs=[(2,[(0,1)]*3),(4,list(combinations(range(4),2))),
            (5,list(combinations(range(5),2))),
            (6,[(i,j) for i in range(3) for j in range(3,6)])]
    n,edges=graphs[1]
    for v in [0,0,4,0]:
        n,edges=triangle_expand(n,edges,v);graphs.append((n,edges))
    yes=no=0;depth=0
    for n,edges in graphs:
        C=cuts(n,edges)
        depth=max(depth,max((sum(s<=t for t in C) for s in C),default=0))
        cycles=cycle_vectors(n,edges)
        for it in range(30):
            chosen=rng.choice(cycles)
            rules={}
            for k in C.values():
                if rng.randrange(5):
                    keep={a for a in ev if rng.randrange(2)}
                    if it%2:keep.add(sum(((chosen>>i)&1)<<j for j,i in enumerate(k)))
                    rules[k]=keep
            pins={i:((chosen>>i)&1 if it%2 else rng.randrange(2))
                  for i in range(len(edges)) if rng.randrange(6)==0}
            got=solve(n,edges,rules,pins)
            expected=any(valid(m,edges,rules,pins) for m in cycles)
            assert (got is not None)==expected,(n,rules,pins,got,expected)
            if got is not None:assert valid(got,edges,rules,pins)
            yes+=expected;no+=not expected
    print("128 socket signatures, full systems:",yes,"YES,",no,"NO; max shore chain",depth)

if __name__=="__main__":main()

"""Physical tree/cyclic component versus the bridge criterion after the two-port reduction."""
from itertools import product
from collections import Counter
from random import Random
import networkx as nx

def sample(k,cycles,r):
    # Vertices 0..k-1 are distinct leaves, including marked leaves 0 and 1.
    g=nx.Graph();g.add_edges_from((k,i) for i in range(3))
    for i in range(3,k):
        a=r.randrange(i);b=next(iter(g[a]));x=max(g)+1
        # Reserve the leaf-number range.
        g.remove_edge(a,b);g.add_edges_from(((a,x),(x,b),(x,i)))
    for _ in range(cycles):
        edges=r.sample(list(g.edges),2);mid=[]
        for a,b in edges:
            x=max(g)+1;g.remove_edge(a,b);g.add_edges_from(((a,x),(x,b)));mid.append(x)
        g.add_edge(*mid)
    return g

def returns(g,k):
    order={v:list(g[v]) for v in g};internal=[v for v in g if len(order[v])==3]
    for bits in product((1,-1),repeat=len(internal)):
        sign=dict(zip(internal,bits));out=[]
        for a in range(k):
            u,v=a,order[a][0]
            while v>=k:
                w=order[v][(order[v].index(u)+sign[v])%3]
                u,v=v,w
            out.append(v)
        yield out

def predicted(g,k):
    u,v=[next(iter(g[a])) for a in (0,1)]
    h=nx.MultiGraph(g);h.remove_nodes_from(range(k));hub=-1
    for a in range(2,k):h.add_edge(hub,next(iter(g[a])))
    bridges=list(nx.bridges(h));body=h.copy();body.remove_edges_from(bridges)
    blocks=list(nx.connected_components(body));ix={x:i for i,B in enumerate(blocks) for x in B}
    tree=nx.Graph();tree.add_nodes_from(range(len(blocks)));tree.add_edges_from((ix[a],ix[b]) for a,b in bridges)
    return any(body.subgraph(blocks[j]).number_of_edges() for j in nx.shortest_path(tree,ix[u],ix[v]))

def main():
    rng=Random(105193);count=Counter()
    for k in (3,4,5,6):
        # Full cyclic word has X0,X1, Ylong, X2..X(k−1), Ysingle.
        n=k+2;X=[0,1,*range(3,n-1)]
        for z in range(3):
            for _ in range(4):
                g=sample(k,z,rng);good=False
                for ret in returns(g,k):
                    native={x:(X[ret[i]]+1)%n for i,x in enumerate(X)}
                    native[2]=0;native[n-1]=3  # deterministic Y swap followed by hub
                    a=native[0]
                    while a!=0:
                        if a==1:good=True;break
                        a=native[a]
                    if good:break
                assert good==predicted(g,k)
                count[good]+=1
    print('48 native two-component cases versus monofacial corridor:',dict(count))
if __name__=='__main__':main()

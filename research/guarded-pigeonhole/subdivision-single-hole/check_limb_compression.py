from itertools import product
from collections import Counter
import networkx as nx
from limb_compression import compress_limb,representative,shrink,lift,check_host
from matching_multipole import solve
from check_matching_multipole import brute_signatures


def unique(g):
    h=nx.MultiGraph()
    h.add_nodes_from(g)
    for i,(u,v) in enumerate(g.edges()):h.add_edge(u,v,key=i)
    return h


def scan():
    checked=patterns=0
    for g in nx.graph_atlas_g():
        if not g or not nx.is_connected(g) or not nx.is_bipartite(g) or max(dict(g.degree()).values())>3:continue
        tips=[v for v in g for _ in range(3-g.degree(v))]
        if len(tips)>5:continue
        h,ports=compress_limb(unique(g),tips)
        sig=brute_signatures(g,tips)
        for c in product(range(3),repeat=len(tips)):
            status,_=solve(h,ports,c)
            assert (status=='SAT')==(c in sig)
        checked+=1;patterns+=3**len(tips)
    return checked,patterns


def expand(g,v):
    cube=nx.cubical_graph()
    neighbors=sorted(cube[0])
    cube.remove_node(0)
    off=max(g)+1
    cube=nx.relabel_nodes(cube,lambda x:off+x)
    old=sorted(g[v])
    g.remove_node(v)
    return nx.compose(g,cube),list(zip(old,[off+w for w in neighbors]))


if __name__=='__main__':
    print('Atlas graphs/patterns:',scan())
    # Large two-port bridge chain of double-edge blocks, each vertex has ordinary degree
    # three except the ends; witness lifting uses the historical edge keys.
    chain=nx.MultiGraph()
    for i in range(12):
        chain.add_edges_from([(2*i,2*i+1)]*2)
        if i:chain.add_edge(2*i-1,2*i)
    chain=unique(chain)
    terms=[0,23]
    reduced,rports,logs=shrink(chain,terms)
    assert len(reduced)==2 and logs
    for c in product(range(3),repeat=2):
        st,w=solve(reduced,rports,c)
        assert (st=='SAT')==(c[0]==c[1])
        if w:
            full=lift(logs,c,{k:color for (_,k),color in w.items()})
            assert check_host(chain,terms,c,full)
    g=nx.complete_graph(4)
    for v in (0,1):
        g,joins=expand(g,v);g.add_edges_from(joins)
    g=unique(g)
    core,_,logs=shrink(g,[])
    assert len(core)==4 and len(logs)>=2
    # K4 has a unique partition into its three pairs of opposite edges.
    assigned={}
    for u,v,k in core.edges(keys=True):
        if k in assigned:continue
        c=len(assigned)//2
        assigned[k]=c
        j=next(t for a,b,t in core.edges(keys=True) if not {a,b}&{u,v})
        assigned[j]=c
    assert check_host(core,[],[],assigned)
    full=lift(logs,[],assigned)
    assert check_host(g,[],[],full)
    print('Bridge-chain and nonbipartite K4-core lifts passed;',len(logs),'reversed substitutions.')
    for k in (0,2,3,4,5):
        h,p=representative(k)
        shore=nx.bipartite.color(h)
        delta=sum(2*shore[v]-1 for v in h)
        valid=0
        for c in product(range(3),repeat=k):
            balanced=all(sum(2*shore[v]-1 for v,t in zip(p,c) if t==a)==delta for a in range(3))
            status,w=solve(h,p,c)
            assert (status=='SAT')==balanced
            valid+=balanced
        print('Representative width/signature size:',k,valid)
    large,p=representative(5)
    moved=[]
    for i,v in enumerate(p):
        a,b=7+2*i,8+2*i
        large.add_edge(v,a);large.add_edges_from([(a,b)]*2)
        moved.append(b)
    large=unique(large)
    from limb_compression import substitute
    core,ctips,log=substitute(large,moved,set(large))
    assert (len(large),len(core))==(17,7)
    for c in product(range(3),repeat=5):
        st,w=solve(core,ctips,c)
        expected,_=solve(large,moved,c)
        assert st==expected
        if st=='SAT':
            full=lift([log],c,{k:t for (_,k),t in w.items()})
            assert check_host(large,moved,c,full)
    print('All 243 terminal patterns verified after transferring five named tips across bridge chains.')

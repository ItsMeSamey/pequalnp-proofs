"""Decision-preserving replacement of small-boundary bipartite cubic limbs.

Hosts are loopless nx.MultiGraphs on integer vertices with globally unique integer
edge keys. The ordered list of external port holders may contain repeats.
"""
from itertools import combinations
import networkx as nx
from matching_multipole import solve,valid_coloring


def representative(k):
    g=nx.MultiGraph()
    if k==0:g.add_edges_from([(0,1)]*3);return g,[]
    if k==2:g.add_edges_from([(0,1)]*2);return g,[0,1]
    if k==3:g.add_node(0);return g,[0]*3
    if k==4:g.add_edges_from([(0,1),(1,2),(2,3),(3,0)]);return g,[0,1,2,3]
    if k==5:
        for i,(u,v) in enumerate([(0,1),(1,2),(2,0),(1,2)],3):
            g.add_edges_from([(u,i),(i,v)])
        return g,[0,3,4,5,6]
    raise ValueError('invalid block boundary size')


def compress_limb(g,ports):
    """Return an equivalent tiny graph with ports in the original order."""
    if not len(g) or not nx.is_connected(g) or len(ports)>5:raise ValueError('unsupported limb')
    if any(g.degree(v)+ports.count(v)!=3 for v in g):raise ValueError('noncubic limb')
    shore=nx.bipartite.color(g)
    fragments=g.copy()
    bridges=[]
    for u,v in nx.bridges(g):
        key=next(iter(g[u][v]))
        bridges.append((u,v))
        fragments.remove_edge(u,v,key)
    parts=list(nx.connected_components(fragments))
    owner={v:i for i,p in enumerate(parts) for v in p}
    tree=nx.Graph()
    tree.add_nodes_from(range(len(parts)))
    ends=[[] for _ in parts]
    for i,v in enumerate(ports):ends[owner[v]].append((('outer',i),v))
    marked={i for i in tree if ends[i]}
    for u,v in bridges:
        a,b=owner[u],owner[v]
        tree.add_edge(a,b)
        ends[a].append((('link',b),u))
        ends[b].append((('link',a),v))
    if any(tree.degree(i)==1 and i not in marked for i in tree):
        raise ValueError('bridge isolates a terminal-free side: no coloring')
    if len(ports) in (0,2):
        # With two ends every bridge-tree chain carries their common color.
        # With no ends a connected cubic bipartite graph always colors.
        return representative(len(ports))
    keep={i for i in tree if len(ends[i])!=2}
    result=nx.MultiGraph()
    holder={}
    for i in sorted(keep):
        h,stubs=representative(len(ends[i]))
        side=nx.bipartite.color(h)
        wanted=[shore[v] for _,v in ends[i]]
        if sorted(side[v] for v in stubs)!=sorted(wanted):
            side={v:1-x for v,x in side.items()}
        offset=len(result)
        result.add_nodes_from(offset+v for v in h)
        for u,v in h.edges():result.add_edge(offset+u,offset+v)
        for label,v in ends[i]:
            j=next(j for j,p in enumerate(stubs) if side[p]==shore[v])
            holder[i,label]=offset+stubs.pop(j)
    output=[None]*len(ports)
    for i in sorted(keep):
        for label,_ in ends[i]:
            a=i
            target=label
            local=holder[i,label]
            while target[0]=='link':
                b=target[1]
                if b in keep:
                    if i<b:result.add_edge(local,holder[b,('link',a)])
                    break
                through=[edge for edge,_ in ends[b] if edge!=('link',a)]
                assert len(through)==1
                a,target=b,through[0]
            else:
                output[target[1]]=local
    assert all(v is not None for v in output)
    return result,output


def substitute(g,ports,S):
    """Try one strictly shrinking substitution; save data needed for exact witness lift."""
    block=g.subgraph(S).copy()
    if not nx.is_connected(block) or not nx.is_bipartite(block):return None
    outer=[i for i,v in enumerate(ports) if v in S]
    cuts=[]
    for u,v,k in g.edges(keys=True):
        if (u in S)!=(v in S):cuts.append((u,v,k) if u in S else (v,u,k))
    terminals=[ports[i] for i in outer]+[u for u,v,k in cuts]
    if len(terminals)>5:return None
    rep,tips=compress_limb(block,terminals)
    if len(rep)>=len(block):return None
    offset=max(g)+1
    key=max((k for _,_,k in g.edges(keys=True)),default=-1)+1
    nxt=g.copy();nxt.remove_nodes_from(S)
    nxt.add_nodes_from(offset+v for v in rep)
    added=set()
    for u,v in rep.edges():
        nxt.add_edge(offset+u,offset+v,key=key)
        added.add(key);key+=1
    newports=list(ports)
    for i,v in zip(outer,tips):newports[i]=offset+v
    for (_,v,k),a in zip(cuts,tips[len(outer):]):nxt.add_edge(offset+a,v,key=k)
    return nxt,newports,(block,terminals,outer,[k for _,_,k in cuts],added)


def shrink(g,ports):
    """Find every type of eligible limb by enumerating cuts, restarting after a shrink."""
    logs=[]
    while True:
        edge_list=list(g.edges(keys=True))
        seen=set()
        chosen=None
        for size in range(min(5,len(edge_list))+1):
            for cut in combinations(edge_list,size):
                # A component of the graph with these edges removed is the candidate.
                blocked={k for u,v,k in cut}
                view=nx.subgraph_view(g,filter_edge=lambda u,v,k:k not in blocked)
                for comp in nx.connected_components(view):
                    S=frozenset(comp)
                    if S in seen:continue
                    seen.add(S)
                    chosen=substitute(g,ports,S)
                    if chosen:break
                if chosen:break
            if chosen:break
        if not chosen:return g,ports,logs
        g,ports,log=chosen
        logs.append(log)


def lift(logs,port_colors,edge_colors):
    """Original keyed-edge assignment from a verified colored core and its port colors."""
    answer=dict(edge_colors)
    for block,terminals,outer,cuts,added in reversed(logs):
        colors=[port_colors[i] for i in outer]+[answer[k] for k in cuts]
        status,w=solve(block,terminals,colors)
        if status!='SAT':raise ValueError('core witness is incompatible with recorded limb')
        for k in added:answer.pop(k)
        for (ends,k),c in w.items():answer[k]=c
    return answer


def check_host(g,ports,port_colors,edge_colors):
    keyed={(frozenset((u,v)),k):edge_colors.get(k) for u,v,k in g.edges(keys=True)}
    return valid_coloring(g,ports,port_colors,keyed)

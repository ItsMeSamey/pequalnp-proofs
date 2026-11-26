from itertools import product
from pathlib import Path
import sys
import networkx as nx
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'subdivision-single-hole'))
from matching_multipole import solve,extend_matching

def edge(u,v):
    return tuple(sorted((u,v)))

def has_pm(g):
    return 2*len(nx.max_weight_matching(g,maxcardinality=True))==len(g)

def table_entry(g,ports,colors):
    status,_=solve(g,ports,colors)
    if status!='UNKNOWN':return status
    if all(g.degree(v)==2 for v in g):
        cy=nx.find_cycle(g)
        for parity in (0,1):
            if extend_matching(g,ports,colors,2,cy[parity::2]) is not None:return 'SAT'
        return 'UNSAT'
    return 'UNKNOWN'

def decide(g,external,shore,entry_oracle=table_entry):
    # External entries are (vertex, color); both nonred colors are 0 and 1.
    assert all(g.degree(v)+sum(w==v for w,c in external)==3 for v in g)
    assert all(c in (0,1) for v,c in external)
    if not has_pm(g):return 'UNSAT',[],[]
    a=nx.Graph();a.add_nodes_from(g)
    a.add_edges_from((u,v) for u,v in g.edges if has_pm(g.subgraph(set(g)-{u,v})))
    blocks=list(nx.connected_components(a))
    bid={v:i for i,b in enumerate(blocks) for v in b}
    dag=nx.DiGraph();dag.add_nodes_from(range(len(blocks)))
    incoming=[[] for _ in blocks];outgoing=[[] for _ in blocks]
    boundary=[[] for _ in blocks]
    for v,c in external:boundary[bid[v]].append((v,c))
    for e in set(edge(*x) for x in g.edges)-set(edge(*x) for x in a.edges):
        u,v=e
        if shore[u]:u,v=v,u
        dag.add_edge(bid[u],bid[v])
        outgoing[bid[u]].append((e,u));incoming[bid[v]].append((e,v))
    assert nx.is_directed_acyclic_graph(dag)
    widths=[];sizes=[];states={():True};front=[]
    for i in nx.topological_sort(dag):
        local=a.subgraph(blocks[i]);ins=incoming[i];outs=outgoing[i]
        done={e for e,v in ins}; remain=[e for e in front if e not in done]
        fresh=[e for e,v in outs];nextstates={}
        ports=[v for v,c in boundary[i]]+[v for e,v in ins+outs]
        cache={}
        for bits,cert in states.items():
            old=dict(zip(front,bits))
            pre=[c for v,c in boundary[i]]+[old[e] for e,v in ins]
            for tail in product((0,1),repeat=len(outs)):
                colors=tuple(pre)+tail
                if colors not in cache:cache[colors]=entry_oracle(local,ports,colors)
                status=cache[colors]
                if status=='UNSAT':continue
                key=tuple(old[e] for e in remain)+tail
                nextstates[key]=nextstates.get(key,False) or (cert and status=='SAT')
        front=remain+fresh;states=nextstates
        widths.append(len(front));sizes.append((len(local),len(ports)))
    return ('SAT' if states.get(()) else 'UNKNOWN' if () in states else 'UNSAT'),widths,sizes

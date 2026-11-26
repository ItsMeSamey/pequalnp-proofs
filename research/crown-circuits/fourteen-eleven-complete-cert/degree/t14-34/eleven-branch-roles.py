"""Evaluate each possible branching flag using the preserved opposite-edge witnesses."""
import csv
from pathlib import Path
import networkx as nx
import sys
root=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(root/'verification/fourteen-nine-host'))
from q11_peeled_spoilers import quota
atlas=nx.graph_atlas_g()
from functools import lru_cache
@lru_cache(None)
def ident(code):
    g=nx.from_graph6_bytes(code)
    return next(i for i,h in enumerate(atlas) if len(h)==len(g) and h.number_of_edges()==g.number_of_edges() and nx.is_isomorphic(g,h))
def component_id(g):
    return ident(nx.to_graph6_bytes(g,header=False).strip())
floor_src=root/'degree/t14-34/eleven-atlas.tsv'
local_floors={}
for row in csv.DictReader(floor_src.open(),delimiter='\t'):
    for g,f in zip(row['graphs'].split(','),row['local_OR_floors'].split(',')):
        local_floors[int(g[1:])]=int(f)
def after(g,q,w,other):
    body=g.copy()
    body.remove_node(w)
    q=q.copy()
    for i,d in body.degree():
        if d:
            essential=any(body.degree(x)>1 for x in body[i])
            q[i]=max(q[i],quota(other,d,15,7,essential))
    cost=0
    for vertices in nx.connected_components(body):
        h=body.subgraph(vertices)
        rich=any(q[i] and q[j] for i,j in h.edges())
        cost+=max(len(h)-1+int(rich),sum(bool(q[i]) for i in h))
    blocks=[body.subgraph(s) for s in nx.connected_components(body) if len(s)>=2]
    opposite=atlas[other]
    marks=[max((quota(component_id(k),d,15,7,any(opposite.degree(x)>1 for x in opposite[i])) for k in blocks),default=0) for i,d in opposite.degree()]
    erase=max(len(opposite)-1+int(any(marks[i] and marks[j] for i,j in opposite.edges())),sum(bool(x) for x in marks))
    for k in blocks:
        f=local_floors.get(component_id(k),0)
        for h in blocks:
            if h is not k:f+=len(h)-1
        if body.number_of_edges()>=2 and erase+f>7:return 99
    return cost
with (root/'verification/fourteen-nine-host/q11-peeled-spoilers.tsv').open() as src,Path(__file__).with_suffix('.tsv').open('w') as out:
    print('graphs','left_branch_flags','right_branch_flags',sep='\t',file=out)
    wins=[]
    for r in csv.DictReader(src,delimiter='\t'):
        if r['reject']!='0' or r['orders']!='5,6': continue
        a,b=[atlas[int(g[1:])] for g in r['graphs'].split(',')]
        fa,fb=map(int,r['floors'].split(','))
        sides=[]
        for g,q,f,other in [(a,r['left_vertex_quotas'],fb,int(b.name[1:])),(b,r['right_vertex_quotas'],fa,int(a.name[1:]))]:
            marks=list(map(int,q.split(',')))
            sides.append([w for w,d in g.degree() if d>=2 and 2+after(g,marks,w,other)+f<=9])
        if not any(sides):wins.append(r['graphs'])
        print(r['graphs'],*(','.join(map(str,x)) or '-' for x in sides),sep='\t',file=out)
    print('all flags excluded',len(wins),wins)

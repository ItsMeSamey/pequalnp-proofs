"""Enumerate necessary pure/mixed/private role assignments on the residual 5+6 pairs."""
import csv,itertools
from pathlib import Path
import networkx as nx
root=Path(__file__).resolve().parents[2]
atlas=nx.graph_atlas_g()
def roles(g,allowed,limit):
    distance=dict(nx.all_pairs_shortest_path_length(g))
    options=[['m']+(['p'] if g.degree(w)>=2 else [])+(['b'] if w in allowed else []) for w in g]
    out=set()
    for labels in itertools.product(*options):
        b=[w for w in g if labels[w]=='b']
        p=[w for w in g if labels[w]=='p']
        m=[w for w in g if labels[w]=='m']
        d=[w for w in p if g.degree(w)==2]
        private_edges=sum(labels[u]==labels[v]=='p' for u,v in g.edges())
        bd=sum(g.degree(w)==2 for w in b)
        if private_edges>1 or bd>1:continue
        if any(labels[u]!='m' and labels[v]!='m' and g.degree(u)==g.degree(v)==2 for u,v in g.edges()):continue
        if any(labels[u]==labels[v]=='b' and max(g.degree(u),g.degree(v))<=3 for u,v in g.edges()):continue
        exc=len(g)-len(m)-len(d)
        debit=len(m)+len(d)
        if exc<=1:debit=len(g)
        for w in b:
            if g.degree(w)<=3:
                debit=max(debit,len(m)+len(d)+max(0,2-sum(distance[w][v]>2 for v in m)))
        if debit>limit:continue
        out.add((int(bool(b)),bd,private_edges))
    return out
floors={}
for r in csv.DictReader((root/'degree/t14-34/eleven-atlas.tsv').open(),delimiter='\t'):
    floors[r['graphs']]=list(map(int,r['local_OR_floors'].split(',')))
src=Path(__file__).with_name('eleven-branch-roles.tsv')
with src.open() as f,Path(__file__).with_suffix('.tsv').open('w') as out:
    print('graphs','result',sep='\t',file=out);wins=[];left=0
    for r in csv.DictReader(f,delimiter='\t'):
        gs=[atlas[int(g[1:])] for g in r['graphs'].split(',')]
        opts=[[int(x) for x in r[k].split(',') if x!='-'] for k in ('left_branch_flags','right_branch_flags')]
        if not any(opts):continue
        a,b=[roles(gs[i],opts[i],9-floors[r['graphs']][1-i]) for i in (0,1)]
        ok=any((u[0] or v[0]) and u[1]+v[1]<=1 and u[2]+v[2]<=1 for u,v in itertools.product(a,b))
        if not ok:wins.append(r['graphs'])
        else:left+=1
        print(r['graphs'],'open' if ok else 'excluded',sep='\t',file=out)
    print(len(wins),wins,'remaining',left)

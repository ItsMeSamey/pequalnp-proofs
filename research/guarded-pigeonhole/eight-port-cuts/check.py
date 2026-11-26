from itertools import permutations,product
from pathlib import Path
import sys
import networkx as nx
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'subdivision-single-hole'))
from matching_multipole import solve
def proper(g,ports,colors):
    masks={v:0 for v in g}
    for v,c in zip(ports,colors):
        if masks[v]>>c&1:return False
        masks[v]|=1<<c
    def rec(edges):
        if not edges:return True
        m,i=min(((7&~(masks[u]|masks[v]),i) for i,(u,v) in enumerate(edges)),key=lambda x:x[0].bit_count())
        u,v=edges[i]
        while m:
            b=m&-m;m-=b;masks[u]|=b;masks[v]|=b
            if rec(edges[:i]+edges[i+1:]):return True
            masks[u]^=b;masks[v]^=b
        return False
    return rec(list(g.edges))
def dec(g,ports,colors,split,oracle=solve):
    outside=set(g)-split
    cut=[(u,v) if u in split else (v,u) for u,v in g.edges if (u in split)!=(v in split)]
    unknown=False
    for opts in product(range(3),repeat=len(cut)):
        answers=[]
        for k,side in enumerate((split,outside)):
            fixed=[(v,c) for v,c in zip(ports,colors) if v in side]
            fixed.extend((pair[k],c) for pair,c in zip(cut,opts))
            pp,cc=zip(*fixed)
            answers.append(oracle(g.subgraph(side),pp,cc)[0])
        if answers==['SAT','SAT']:return 'SAT'
        if 'UNSAT' not in answers:unknown=True
    return 'UNKNOWN' if unknown else 'UNSAT'
def example(rows):
 n=len(rows)
 g=nx.Graph((i,n+j) for i,r in enumerate(rows) for j in range(n) if r>>j&1)
 pp=[v for v in range(2*n) if g.degree(v)==2]
 assert len(pp)==6
 return g,pp
for rows in ([6,5,3],[9,10,12,7],[9,10,24,21,22]):
    original,pp=example(rows)
    results=[]
    for pi in permutations((0,1,2)):
        cc=[0,1,2]+list(pi)
        wanted=proper(original,pp,cc)
        # Add opposite-shore edges from both red holders to an independent C6 cap.
        cap,tp=example([6,5,3]); off=len(original)
        g=nx.compose(original,nx.relabel_nodes(cap,{v:off+v for v in cap}))
        a,b=[v for v,c in zip(pp,cc) if c==2]
        g.add_edges_from([(a,off+3),(b,off)])
        ext=[(v,c) for v,c in zip(pp,cc) if c!=2]+[(off+i,c) for i,c in [(1,0),(4,0),(2,1),(5,1)]]
        ports,colors=zip(*ext)
        assert proper(g,ports,colors)==wanted
        split=set(original)
        def exact_local(h,p,c):return ('SAT' if proper(h,p,c) else 'UNSAT'),None
        assert (dec(g,ports,colors,split,exact_local)=='SAT')==wanted
        result=dec(g,ports,colors,split)
        assert result=='UNKNOWN' or (result=='SAT')==wanted
        results.append(wanted)
    print(rows,results)

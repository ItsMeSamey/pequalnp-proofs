"""Component star spoiler quotas; no SAT or native search."""
from collections import Counter
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import csv
import networkx as nx
root=Path(__file__).resolve().parents[2]
atlas=nx.graph_atlas_g()
cost={2:1,3:4,4:7,5:10,6:13,7:16,8:19,9:21,10:24,11:27,12:29,13:32}
def blocked(n,size,ors):
    if n not in cost:return False
    return size<cost[n] or ors<max(0,2*n-4) or (n==9 and size==21 and ors<17)
@lru_cache(None)
def quota(g,d,size,ors):
    # How many edge labels must spoil? A set of safe labels cannot contain
    # any subset meeting the minor contradictions. Enumerate it exactly.
    edges=list(atlas[g].edges());m=len(edges);unsafe=[False]*(1<<m)
    endpoints=[(1<<i)|(1<<j) for i,j in edges]
    for s in range(1,1<<m):
        t=s.bit_count()
        if any(unsafe[s^(1<<j)] for j in range(m) if s>>j&1):
            unsafe[s]=True;continue
        v=0
        for j,e in enumerate(endpoints):
            if s>>j&1:v|=e
        bank=2*t-v.bit_count()
        unsafe[s]=blocked(t+d,bank+size-1,bank+ors)
    return m-max(s.bit_count() for s,x in enumerate(unsafe) if not x)
def main():
    totals=Counter(); path=Path(__file__).with_name('q11-spoilers.tsv')
    with open(root/'degree/t14-34/eleven-atlas.tsv') as fp,path.open('w') as out:
        print('orders','graphs','floors','left_vertex_quotas','right_vertex_quotas','reject',sep='\t',file=out)
        for row in csv.DictReader(fp,delimiter='\t'):
            if row['orders'] not in ('4,7','5,6'):continue
            a,b=[int(s[1:]) for s in row['graphs'].split(',')];fa,fb=map(int,row['local_OR_floors'].split(','))
            def quotas(src,dst):return [quota(dst,atlas[src].degree(i),17,9) for i in range(len(atlas[src]))]
            qa,qb=quotas(a,b),quotas(b,a)
            def debit(src,q):
                if any(q[i] and q[j] for i,j in atlas[src].edges()):return len(q)
                return max(len(q)-1,sum(k>0 for k in q))
            reject=(debit(a,qa)+fb>9 or debit(b,qb)+fa>9)
            print(row['orders'],row['graphs'],row['local_OR_floors'],','.join(map(str,qa)),','.join(map(str,qb)),int(reject),sep='\t',file=out)
            totals[row['orders'],reject]+=1
    print(totals)
if __name__=='__main__':main()

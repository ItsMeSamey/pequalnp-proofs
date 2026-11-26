from q11_peeled_spoilers import quota,atlas
from pathlib import Path
from itertools import combinations
import csv,networkx as nx
root=Path(__file__).resolve().parent
rows=csv.DictReader((root/'q11-peeled-spoilers.tsv').open(),delimiter='\t')
out=(root/'q11-four-strips.tsv').open('w')
print('graphs','original','strip',sep='\t',file=out)
count=old=0
for row in rows:
 if row['orders']!='5,6':continue
 a,b=[int(s[1:]) for s in row['graphs'].split(',')]
 fa,fb=map(int,row['floors'].split(','))
 answer='';previous=int(row['reject']);old+=previous
 for src,dst,q,floor in ((a,b,row['left_vertex_quotas'],fb),(b,a,row['right_vertex_quotas'],fa)):
  G=atlas[src];q=list(map(int,q.split(',')));erased=len(G)-4
  if 4+erased+floor<=9:continue
  for keep in combinations(G.nodes(),4):
   K=G.subgraph(keep)
   if K.number_of_edges()<5:continue
   # Connected four-flag skeleton, so the outside flags can be peeled for one OR each.
   universal=[y for y in keep if K.degree(y)==3]
   marked=[y for y in universal if q[y] or quota(dst,3,17-erased,9-erased,True)]
   if len(marked)>=2:
    answer=f'{src}:'+','.join(map(str,keep))+':'+','.join(map(str,marked));break
  if answer:break
 count+=bool(answer) and not previous
 print(row['graphs'],previous,answer or '-',sep='\t',file=out)
print('previous',old,'additional strips',count,'remaining',281-old-count)

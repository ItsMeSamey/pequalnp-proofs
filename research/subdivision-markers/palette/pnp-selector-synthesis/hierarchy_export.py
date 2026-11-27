from hierarchy import circuits
from rank7_missing import cols
from wedge_checks import direct
from recognizer import tag_at
from frontier import basis
from wedge_path import coordinates
from seven_terminal_check import kernel
_,L=direct(cols)
print(*(sum(((x>>i)&1)<<j for j,x in enumerate(L)) for i in range(len(cols))))
cs=circuits(cols);print(len(cs),*cs)
print(64)
for g in range(64):
 ids=[i for i,(k,b) in enumerate(cols) if tag_at(g,k,3)==b]
 gg=[]
 for z in kernel([cols[i][0] for i in ids]):
  u=sum(1<<i for j,i in enumerate(ids) if z>>j&1)
  gg.append(coordinates(u,L))
 print(len(gg),*gg)

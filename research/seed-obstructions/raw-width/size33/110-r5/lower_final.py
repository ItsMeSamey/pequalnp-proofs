import os,sys
os.environ['LOW_WIDTH']='22'
sys.path.insert(0,'/workspace/scratch/syn_bounds/s33-low/all22-four')
from group_roles import Rbank,qs,info,test
for k,i,C in ((110,91,(129,523)),(142,123,(354,4160))):
 assert set(Rbank(i))==set(qs)|set(C)
 for m in (38,42,46,127):
  O=tuple(j for j in range(7) if m>>j&1)
  slack=12-7+len(O)-len(info(O,i)[2])
  res=[test(O,[i],a,10000) for a in range(slack+1)]
  assert all(v is False for v in res)
  print(k,m,res)

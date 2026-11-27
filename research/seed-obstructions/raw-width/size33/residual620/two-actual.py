import os, sys
from pathlib import Path
os.environ['LOW_WIDTH']='22'
sys.path.insert(0,'/workspace/scratch/syn_bounds/s33-low/all22-four')
from group_roles import Rbank,info,test
for label,i,extra in ((120,101,{177,523}),(143,124,{354,4184})):
 assert set(Rbank(i))=={1<<j for j in range(13)}|extra
 for O in ((1,2,3,5),tuple(range(7))):
  slack=12-(7-len(O)+len(info(O,i)[2]))
  outcomes=[test(O,[i],a,10000) for a in range(slack+1)]
  assert slack==3 and all(x is False for x in outcomes)
  print(label,i,O,outcomes)

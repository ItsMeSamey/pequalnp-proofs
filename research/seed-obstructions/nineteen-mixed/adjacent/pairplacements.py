import os,sys
from pathlib import Path
fallback=Path(__file__).resolve().parents[2]/'ordinary-line-nine'
sys.path.insert(0,os.environ.get('LINE19_VERIFIER',str(fallback)))
from finaledge import group,perm
from compartments import test
from edge import *
if __name__=='__main__':
 grp=group()
 cases=set()
 for a,b in combinations([x for x in range(128) if x.bit_count()==2],2):
  f=failures(a,b)
  if len(f)!=2 or not a&b:continue
  for s,r in [(a,b),(b,a)]:cases.add(min((perm(s,g),perm(r,g)) for g in grp))
 assert len(cases)==11
 for a,b in sorted(cases):
  t,=inside(a&~b);c,=inside(a&b);print('bank',a,b,t,c,flush=True)
  for loc in product(range(3),repeat=2):
   if loc==(2,2): continue
   lo=test(a,b,t,c,loc,threshold=5,no_or=True)
   hi=test(a,b,t,c,loc,threshold=6)
   assert not lo and not hi,(a,b,loc,lo,hi)
   print(loc,lo,hi,flush=True)

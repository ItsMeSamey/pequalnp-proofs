from pathlib import Path
from itertools import combinations
from collections import Counter
exec(Path('coverage.py').read_text().split('hist=Counter')[0])
assert stars==[708,1416,2832,5664,3137,6274,4357]
cnt=0;banks=0
for s,r in combinations([x for x in range(128) if x.bit_count()==2],2):
 if (s&r).bit_count()!=1:continue
 a=(s&r).bit_length()-1;b=(s&~r).bit_length()-1;c=(r&~s).bit_length()-1
 cs=stars[a]&stars[b];cr=stars[a]&stars[c]
 if cs==cr:continue
 banks+=1
 for t,u,mt,mu in ((b,c,cs,cr),(c,b,cr,cs)):
  for p in range(13):
   if stars[t]>>p&1:continue
   for q in range(13):
    if not ((stars[u]&~stars[t]&~mu)>>q&1):continue
    for w,W in enumerate(stars):
     if w==t:continue
     G=W&~((cs|cr) if w==a else mu if w==u else 0)
     assert any(z&(1<<(13+t)) and z&(1<<p) and z&(1<<q) and z&G for z in ng)
     cnt+=1
print(banks,'nonconcurrent adjacent banks;',cnt,'individual extensions')

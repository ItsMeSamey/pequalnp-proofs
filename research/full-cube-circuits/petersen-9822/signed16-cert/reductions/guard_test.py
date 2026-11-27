from pathlib import Path
from three_bins import V,subs,neighbors,N
from functools import cache
from collections import Counter
@cache
def possible(S,T,U,i):
 assert i&U
 for t in subs(T):
  if neighbors(t)&t:continue
  seen=set()
  for s in subs(S):
   if neighbors(s|t)&(s|t):continue
   q=neighbors(s|t)&U
   if q&i or N[i]&U&~q:
    seen.add(q)
    if len(seen)>1:return False
 return True

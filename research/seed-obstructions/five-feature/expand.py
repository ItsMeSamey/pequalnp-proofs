from ast import literal_eval
from itertools import combinations_with_replacement
p=set()
for line in open('seq-hard'):
 _,_,_,_,aa,bb,c=literal_eval(line)
 for a in combinations_with_replacement(aa,3):
  for b in combinations_with_replacement(bb,3):
   if set(a)==set(aa) and set(b)==set(bb):p.add((*a,*b,c))
with open('seq-patterns','w') as f:
 for row in sorted(p):print(*row,file=f)

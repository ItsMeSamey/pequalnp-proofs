import itertools as I
E={tuple(sorted(p)) for p in [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]}
N=lambda a:{b for b in range(11) if tuple(sorted((a,b))) in E}
def edge(a,b):return tuple(sorted((a,b)))
def foot():
 for e,f in I.combinations(sorted(E),2):
  if len(set(e+f))<4:continue
  corners=list(I.product(e,f))
  choices=[(N(a)&N(b))-{*e,*f,3} for a,b in corners]
  for k in I.product(*choices):
   st={edge(a,v) for p,v in zip(corners,k) for a in p}
   if 7 <= len(st) <= 8 and not any(3 in s for s in st):yield e,f,st
for e,f,st in foot():
 print(e,f,sorted(st), 'inc67', sorted(s for s in st if 6 in s or 7 in s))

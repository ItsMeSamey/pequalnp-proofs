from itertools import product
def put(B,x,low=0):
 while x>>low:
  k=x.bit_length()-1
  if k not in B: B[k]=x;return 0
  x^=B[k]
 return x
def solve(C,sw,start,rem):
 global nodes
 nodes+=1
 E={}; ref=None; have=set()
 for d in range(1,32,4):
  B={}; K=[]
  for j,v in enumerate(C[2:],2):
   if (v&d).bit_count()%2:continue
   x=put(B,(v<<25)|(1<<j),25)
   if x:K.append(x)
  x=(2<<25)|2
  while x>>25 and x.bit_length()-1 in B:x^=B[x.bit_length()-1]
  if x>>25:continue
  b=d>>4;have.add(b);x=x*2+b
  if ref is None:ref=x
  put(E,x^ref)
  for k in K:put(E,2*k)
 put(E,2*sw+1)
 if 0 in E:return
 if len(have)==2:print('FOUND',C,sw,flush=True);quit()
 if rem:
  for v in range(start,32):
   if v not in C:solve(C+[v],sw,v+1,rem-1)
nodes=0
for h in product(range(0,32,8),repeat=3):
 C=[1,2,8,4,5^h[0],6^h[1],7^h[2]]
 x=C[3]^C[4]^C[5]^C[6]
 if x&16:continue
 solve(C,120|(4 if x&8 else 0),3,12)
print('clear',nodes)

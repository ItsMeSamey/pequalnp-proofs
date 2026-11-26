exec(open(__import__('pathlib').Path(__file__).with_name('port-four-common-basis-check.py')).read().split('for k in range(1,15):')[0])
P=[z for z in planes if z!=u]
def ort(x):
 return sum(1<<v for v in range(16) if all((v&j).bit_count()%2==0 for j in range(16) if x>>j&1))
def projection(x,p):
 return frozenset(min(v,v^p) for v in range(16) if x>>v&1)
for dual in (False,True):
 targets=[ort(x) if dual else x for x in [u]+P]
 a=targets[0]
 for p in range(1,16):
  if a>>p&1:continue
  pat=projection(a,p)
  for i,z in enumerate(targets[1:]):
   if projection(z,p)==pat:obs[i]|=1<<len(pairs)
  pairs.append(None)
allbits=(1<<len(pairs))-1
for k in range(6,20):
 r=search(allbits,list(range(34)),k)
 print(k,r,flush=True)
 if r is not None:break

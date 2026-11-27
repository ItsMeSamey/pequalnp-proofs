from itertools import combinations
E=[6,24,17,33,66,132,264,528,160,640,576,320,288]
F=lambda x:any(x&e==e for e in E)
N=[x for x in range(1024) if not F(x) and all(F(x|1<<i) for i in range(10) if not x>>i&1)]
hit=[sum(1<<i for i,e in enumerate(E) if x&e) for x in range(1024)]
unions=[0]*65536
for x in range(1,65536):
 b=x&-x;unions[x]=unions[x^b]|N[b.bit_length()-1]
ok=[]
for i,j in combinations(range(16),2):
 forbidden=65535^(1<<i)^(1<<j)
 raw=1023^unions[forbidden]
 assert raw==0
 s=forbidden;terms=set()
 while True:
  a=1023^unions[s];b=1023^unions[forbidden^s]
  if a and b and any((a&N[k]) and (b&N[k]) for k in (i,j)):
   terms.add(hit[a]&hit[b])
  if not s:break
  s=(s-1)&forbidden
 maxterms=[a for a in terms if a and not any(a!=b and a&~b==0 for b in terms)]
 states={0}
 for _ in range(4):states={x|y for x in states for y in maxterms}|states
 if 8191 in states:ok.append((i,j,len(maxterms)))
print('survivors',len(ok),ok)

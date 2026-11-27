import itertools,json,math
from fractions import Fraction as F
from pathlib import Path
E=[6,24,17,33,66,132,264,528,160,640,576,320,288]
Z=[s for s in range(1024) if all(s&e!=e for e in E) and all(any((s|1<<v)&e==e for e in E) for v in range(10) if not(s>>v&1))]
def weight(src):
 w=list(map(F,src));den=math.lcm(*(x.denominator for x in w));return [int(den*x) for x in w],den
def price(R,C,w):
 tab=[[w[16*i+j] for j in C] for i in R]
 if len(R)>len(C):tab=list(zip(*tab))
 stacks=[(0,)*(len(tab[0]) if tab else 0)];best=0
 for t in tab:
  n=[tuple(a+b for a,b in zip(s,t)) for s in stacks];stacks+=n
  best=max(best,max(sum(x for x in s if x>0) for s in n))
 return best
def rawcheck(w,d):
 assert all(price([i for i,e in enumerate(E) if e>>v&1],[j for j,z in enumerate(Z) if not(z>>v&1)],w)<=d for v in range(10))
def lines(path):return list(map(json.loads,Path(path).read_text().splitlines()))
db={tuple(s):weight(w) for s,w in lines('kw-helper.jsonl')+lines('kw-or4.jsonl')}
fresh={(k,tuple(s)):weight(w) for k,s,w in lines('kw-extended-indexed.jsonl')}
for w,d in list(db.values())+list(fresh.values()):rawcheck(w,d)
for k in range(4,11):
 ledger=json.loads(Path(f'reuse-extended{k}.json').read_text())
 if k>4:cases=[(s,lambda x,m=sum(1<<v for v in s):bool(x&m)) for s in itertools.combinations(range(10),k)]
 else:
  cases=[]
  for T in itertools.combinations(range(10),4):
   m=sum(1<<v for v in T);edges=[e for e in E if e&m==e]
   deg=[sum(e>>v&1 for e in edges) for v in T]
   if sorted(deg)!=[1,1,2,2]:continue
   ends=sum(1<<v for v,d in zip(T,deg) if d==1)
   for v in range(10):
    if not(m>>v&1):cases.append(((*T,v),lambda x,v=v,p=edges+[ends]:bool(x>>v&1) or any(x&e==e for e in p)))
 for s,fn in cases:
  key=','.join(map(str,s));w,d=db[tuple(ledger[key])] if key in ledger else fresh[k,s]
  best=max(d,price([i for i,e in enumerate(E) if fn(e)],[j for j,z in enumerate(Z) if not fn(z)],w))
  assert sum(w)>(14 if k==4 else 19-k)*best
 print(k,len(cases),'rational strict bounds')

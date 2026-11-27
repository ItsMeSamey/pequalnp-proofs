from itertools import permutations
from functools import cache
R=list(dict.fromkeys(permutations((0,0,1,2,3))))
words=[sum(x*4**i for i,x in enumerate(t)) for t in R]
labs=list({sum(1<<j for j,t in enumerate(R) if t[i]==t[k]==0) for i in range(5) for k in range(i)})
F=(1<<60)-1
Q={sum(1<<j for j,w in enumerate(words) if (a&w).bit_count()%2) for a in range(1024)}
Q|={F^x for x in Q.copy()}
@cache
def low(p):return sum(bool(a&p) for a in labs)
@cache
def opt(p,b):
 l=low(p)
 if l<2:return l
 if l>b:return b+1
 best=b+1
 for x in {p&q for q in Q if q&(p&-p)}-{p}:
  y=x^p
  if low(x)+low(y)>=best:continue
  k=opt(x,best-1-low(y))
  if k+low(y)>=best:continue
  best=min(best,k+opt(y,best-1-k))
 return best
print('optimum at cap 25',opt(F,25),flush=True)

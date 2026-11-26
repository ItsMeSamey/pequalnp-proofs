import random
R=random.Random(8081)
def bitdot(x,y): return (x&y).bit_count()%2
def chars(f,n,p):
 return [a for a in range(1<<n) if sum(v*(-1)**bitdot(a,x) for x,v in enumerate(f))%p]
def varies(f,P,n,p,d):
 A=chars(f,n,p)
 if not A or d==0: return False
 D=[a^A[0] for a in A[1:]];W={0}
 while D:
  w=max(range(1<<n),key=lambda t:sum(bitdot(t,v) for v in D))
  D=[v for v in D if not bitdot(w,v)]; W|={w^v for v in W}
 shifts=W|{(1<<i)^w for i in range(n) for w in W}
 for v in shifts-{0}:
  h=[a*f[x^v]%p for x,a in enumerate(f)]
  dp=[b^P[x^v] for x,b in enumerate(P)]
  x=next((x for x,a in enumerate(h) if a),None)
  if x is not None and (dp[x] or varies(h,dp,n,p,d-1)): return True
 return False
for it in range(600):
 n=R.randint(1,5); p=R.choice([3,5,7]); N=1<<n;d=R.randint(0,3)
 A={a:R.randrange(1,p) for a in R.sample(range(N),R.randrange(min(N,8)+1))}
 f=[sum(b*(-1)**bitdot(a,x) for a,b in A.items())%p for x in range(N)]
 mons=[a for a in range(N) if a.bit_count()<=d and R.randrange(4)==0]
 P=[sum((x&a)==a for a in mons)%2 for x in range(N)]
 assert varies(f,P,n,p,d)==(len({b for a,b in zip(f,P) if a})>1)
print('600 oracle comparisons passed')

from itertools import product
def coeff(v):
 f=list(v)
 for i in range(4):
  for s in range(16):
   if s>>i&1:f[s]^=f[s^(1<<i)]
 return f
def gauss(f):
 if not any(f):return True
 p=f.index(1)
 g=lambda t:f[p^t]
 m=[g(1<<i) for i in range(4)]
 def w(i,j):return g((1<<i)|(1<<j))^m[i]*m[j]
 def rec(t):
  if not t:return 1
  i=(t&-t).bit_length()-1
  u=t^(1<<i)
  a=m[i]*rec(u)
  for j in range(4):
   if u>>j&1:a^=w(i,j)*rec(u^(1<<j))
  return a
 return all(rec(t)==g(t) for t in range(16))
def gate(kind,a,b,x):return int((a or b or x) if kind=='O' else a==b==x)
def census():
 for A,B,normalized,mask in product('OC','OC',(False,True),range(64)):
  V=[]
  for s in range(16):
   a,b,c,d=[(s^mask)>>i&1 for i in range(4)]
   f=[gate(A,a,b,x^((mask>>4)&1)) for x in (0,1)]
   g=[gate(B,c,d,x^((mask>>5)&1)) for x in (0,1)]
   da,db=f[0]^f[1],g[0]^g[1]
   if normalized:
    value=f[0]*g[0]^da*g[0]^db*f[0]
    grouped=f[1]*g[1]^da*db
   else:
    value=da*g[0]^db*f[0]^da*db
    grouped=f[0]*g[0]^f[1]*g[1]
   assert grouped==value
   V.append(value)
  assert not gauss(coeff(V))
 print('512 complemented OR/COPY pairs: two branches verified; single matching signature rejected')

if __name__=='__main__':
 census()

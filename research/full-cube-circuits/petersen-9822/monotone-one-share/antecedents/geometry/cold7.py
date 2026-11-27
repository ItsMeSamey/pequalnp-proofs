from itertools import combinations
from collections import Counter
V=1023;ALL=(1<<1024)-1
E=[6,24,17,33,66,132,264,528,160,640,576,320,288]
F=sum(1<<m for m in range(1024) if any(m&e==e for e in E))
FALSE=ALL^F
def bits(m):
 while m:b=m&-m;yield b;m^=b
N={b:sum(e^b for e in E if e&b) for b in bits(V)}
def ns(s):
 n=0
 for b in bits(s):n|=N[b]
 return n
def subsets(s):
 t=s
 while t:yield t;t=(t-1)&s
 yield 0
MIS=[m for m in range(1024) if not(ns(m)&m) and not(V&~(m|ns(m)))]
LS={b:sum(1<<m for m in range(1024) if not m&b) for b in bits(V)}
def up(z,s):
 for b in bits(s):z|=(z&LS[b])<<b
 return z
def down(z,s):
 for b in bits(s):z|=(z>>b)&LS[b]
 return z
def proj(z,s):
 for b in bits(s):
  q=(z|(z>>b))&LS[b];z=q|(q<<b)
 return z
def conflict(sections,A):
 ret=[]
 for x,y in combinations(bits(A),2):
  q=LS[x]&LS[y]
  if any(q&n&(n>>x)&(n>>y)&(p>>(x+y)) for p,n in sections) and any(q&n&(p>>x)&(p>>y)&(p>>(x+y)) for p,n in sections):ret.append(x|y)
 return ret
def cover(d,A,k):return any(all(e&r for e in d) for r in subsets(A) if r.bit_count()<=k)
def tables(S,T,U,M,plus=0,minus=0):
 A=S|T;Y=T|U
 hp=1<<M;hn=sum(1<<m for m in MIS if S&~m)|sum(1<<b for b in bits(A))|1
 hp|=plus;hn|=minus
 p0=0;n0=proj(FALSE,S);p1=proj(F,S);n1=0
 while True:
  hp=up(proj(hp,U),A);hn=down(proj(hn,U),A)
  p0=up(proj(p0,S),Y);p1=up(proj(p1|p0,S),Y)
  n1=down(proj(n1,S),Y);n0=down(proj(n0|n1,S),Y)
  if hp&hn or p0&n0 or p1&n1:return None
  nxt=(hp|(F&n0),hn|(FALSE&p1),p0|(F&hn),n1|(FALSE&hp))
  if nxt==(hp,hn,p0,n1):break
  hp,hn,p0,n1=nxt
 return hp,hn,p0,n0,p1,n1
def main():
 ct=Counter()
 for S in range(V):
  size=S.bit_count()
  if size not in (1,2,3) or S&ns(S):continue
  for U in subsets(V&~(S|ns(S))):
   if U.bit_count() not in (2,3):continue
   T=V^S^U;A=S|T;Y=T|U
   if not cover([e for e in E if e&U==e],U,size-1):continue
   for M in MIS:
    if S&~M:continue
    ct['cases']+=1;z=tables(S,T,U,M)
    if not z:continue
    ct['table']+=1;hp,hn,p0,n0,p1,n1=z
    if not cover(conflict([(hp,hn)],A),A,U.bit_count()-2):continue
    ct['inner']+=1
    if not cover(conflict([(p0,n0),(p1,n1)],Y),Y,size-1):continue
    ct['both']+=1;print('left',S,T,U,M,flush=True)
 print(ct)
if __name__=='__main__':main()

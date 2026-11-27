"""Direct finite checks of the nine-gate shared-helper leaf obstruction."""
from itertools import combinations
from collections import Counter
E=(6,24,17,33,66,132,264,528,160,640,576,320,288)
V=1023;F=[any(m&e==e for e in E) for m in range(1024)]
def sub(m):return [v for v in range(1024) if v&m==v]
def bits(m):return [1<<i for i in range(10) if m>>i&1]
def nb(m):return sum(i for i in bits(V) if any(e&i and (e^i)&m for e in E))
Z=[m for m in range(1024) if not F[m] and all(F[m|b] for b in bits(V^m))]
def witness(rows,Q):
 d={}
 for x,y in combinations(bits(Q),2):
  sec={}
  for a in sub(Q^x^y):
   vals=tuple(rows.get(n) for n in (a,a|x,a|y,a|x|y))
   if vals==(0,0,0,1):sec[0]=a
   if vals==(0,1,1,1):sec[1]=a
   if len(sec)==2:
    d[x|y]=[sec[0],sec[1]];break
 return d
def necessary(s,t,m):
 A=s|t;pos={m&A};neg=set(bits(A))|{0}
 for a in sub(t):
  if F[a] or not nb(a)&s:continue
  for b in sub(s):
   (pos if F[a|b] else neg).add(a|b)
 row={}
 for a in sub(A):
  p=any(x&a==x for x in pos);n=any(a&y==a for y in neg)
  if p and n:return None
  if p or n:row[a]=int(p)
 return witness(row,A)
def main():
 count=Counter()
 for s in range(1024):
  if s.bit_count()!=3 or F[s]:continue
  for u in [0,*bits(V^s^nb(s))]:
   t=V^s^u;count['partition']+=1
   for m in Z:
    if s&~m:continue
    d=necessary(s,t,m);count['MIS']+=1
    if d is None:why='monotonicity'
    elif (not d if not u else any(all(k&x for k in d) for x in bits(s|t))):why='OPEN'
    else:why='conflicts'
    count[why]+=1
    if why=='OPEN':print(why,s,t,u,m)
 print(count)
if __name__=='__main__':main()

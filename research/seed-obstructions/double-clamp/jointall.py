from pathlib import Path
exec(Path('coverage.py').read_text().split('hist=Counter')[0])
rows=[tuple(map(int,l.split())) for l in open('allsingle')]
out=open('jointgood','w')
for s,r,lc,k in rows:
 flag=[int(bool(s>>i&1))|int(bool(r>>i&1))*2 for i in range(7)]
 ns=[(n&8191,int(bool(n>>13&s))|int(bool(n>>13&r))*2) for n in ng]
 avail=[T & __import__('functools').reduce(int.__or__,(p for p,g in ns if not f&~g),0) for T,f in zip(stars,flag)]
 hit=[0]*13
 for mask,g in ns:
  labels=sum((1<<t) for t in range(7) if avail[t]&mask and not flag[t]&~g)
  if labels:
   p=mask
   while p:
    v=p&-p;hit[v.bit_length()-1]|=labels;p-=v
 for A in range(1,128):
  if all(A&h for h in hit):print(s,r,A,file=out)
out.close()

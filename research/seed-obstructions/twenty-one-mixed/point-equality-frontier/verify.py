"""Replay the minimum-point-cost mixed frontier at exactly 21 mixed gates."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations
from pathlib import Path
import subprocess, tempfile, sys
from pysat.card import CardEnc
from pysat.solvers import Solver
from input import raw_samples
here=Path(__file__).resolve().parent
P,N,_=raw_samples(here/'L-meta-18968.json')
h=' '.join(map(str,(len(P),len(N),*sorted(P),*sorted(N))))
raw=tuple(1<<i for i in range(7))
stars=tuple(sum({p&8191 for p in P if p&(l<<13)}) for l in raw)
inc=tuple(sum(1<<j for j,s in enumerate(stars) if s>>i&1) for i in range(13))
def move(m,perm):return sum(1<<j for i,j in enumerate(perm) if m>>i&1)
group=[]
for perm in permutations(range(7)):
 ims=tuple(move(x,perm) for x in inc)
 if set(ims)!=set(inc):continue
 pp=tuple(inc.index(v) for v in ims)
 lm=tuple(move(i,perm) for i in range(128))
 def image(r):return move(r&8191,pp)|(lm[r>>13]<<13)
 if all({image(r) for r in rows}==rows for rows in (P,N)):group.append((pp,lm))
assert len(group)==24
rels={(p>>13,n>>13) for p in P for n in N if not (p&8191)&~n}
def minimal_lines(width,previous):
 c=CardEnc.atmost(list(range(1,128)),width,top_id=127).clauses
 c += [[m for m in range(1,128) if p&m and not n&m] for p,n in rels]
 c += [[-m for m in fam] for fam in previous]
 out=set()
 with Solver(name='cadical195',bootstrap_with=c) as s:
  while s.solve():
   f=tuple(sorted(m for m in s.get_model() if 0<m<128))
   assert len(f)==width
   out.add(f);s.add_clause([-v for v in f])
 return out
nine=minimal_lines(9,[raw]);assert len(nine)==24
ten=minimal_lines(10,[raw,*nine]);assert len(ten)==437
assert Counter(sum(m.bit_count()==1 for m in f) for f in ten)=={6:361,5:60,4:16}
point={w:[tuple(map(int,l.split())) for l in (here/f).read_text().splitlines()] for w,f in [(11,'cost-nine-width-eleven.txt'),(12,'cost-five-width-twelve.txt')]}
assert list(map(len,point.values()))==[27,5]
def point_ro_blocks(B):
 def restrictions(p):return sum(1<<j for j,m in enumerate(B) if p&8191&m)
 obligated={r:0 for r in P|N}
 for p in P:
  for n in N:
   if (p>>13)&~(n>>13):continue
   diff=restrictions(p)&~restrictions(n)
   assert diff
   if diff.bit_count()==1:obligated[p]|=diff;obligated[n]|=diff
 graphs=[]
 for rows in (P,N):
  g=[0]*len(B)
  for r in rows:
   s=obligated[r]
   for i in range(len(B)):
    if s>>i&1:g[i]|=s^(1<<i)
  graphs.append(g)
 @lru_cache(None)
 def compatible(s):
  if s.bit_count()<=1:return True
  for g in graphs:
   c=s&-s
   while True:
    d=c
    for i in range(len(B)):
     if c>>i&1:d|=g[i]&s
    if d==c:break
    c=d
   if c!=s:return compatible(c) and compatible(c^s)
  return False
 whole=(1<<len(B))-1
 return compatible(whole) or any(compatible(s) and compatible(whole^s) for s in range(1,whole,2))
assert [point_ro_blocks(b) for b in point[12]]==[True,True,False,True,False]
def sym_points(b):return [(tuple(sorted(move(x,p) for x in b)),lm) for p,lm in group]
def reps(xs,gs):
 left=set(xs)
 while left:
  x=left.pop();orb={tuple(sorted(g[v] for v in x)) for g in gs}
  assert orb-{x}<=left
  left.difference_update(orb);yield x,len(orb)
def line_price(a,b):
 if a.bit_count()<2 or b.bit_count()<2 or a==b:return max(2,a.bit_count(),b.bit_count())
 return (a|b).bit_count()-1-int(not a&b)
def domain(w,l):
 points=point[w]
 if w==12 and l>=9:points=[points[i] for i in (0,1,3)]
 lines=[]
 if l==7:lines=[raw]
 if l==8:lines=[tuple(sorted((*raw,m))) for m in range(128) if w==12 or m.bit_count()<=4]
 if l==9:lines=sorted(set(nine)|{tuple(sorted((*raw,a,b))) for a,b in combinations_with_replacement(range(128),2) if w==12 or line_price(a,b)<=3})
 if l==10 and w==11:
  states={raw}
  for _ in range(3):
   states={tuple(sorted((*s,z))) for s in states for a,b in combinations_with_replacement(s,2) for z in (a&b,a|b)}
  assert len(states)==8275;lines=sorted(states)
 if w==12 and l==10:
  b=points[0]
  assert set(points)=={p for p,_ in sym_points(b)}
  gs=[lm for p,lm in sym_points(b) if p==b];assert len(gs)==8
  for x,k in reps(combinations_with_replacement(range(128),3),gs):
   yield b,(*raw,*x),k*len(points)
  spans={tuple(sorted((*f,m))) for f in nine for m in range(128)}|ten
  # These 24 nine-basis extensions occur in the ordinary portion too.
  duplicate={f for f in spans if set(raw)<=set(f)}
  assert len(duplicate)==24
  for x,k in reps(spans-duplicate,gs):yield b,x,k*len(points)
  return
 out=Counter()
 for b in points:
  ims=sym_points(b);first=min(p for p,_ in ims);gs=[lm for p,lm in ims if p==first]
  for f in lines:out[(first,min(tuple(sorted(g[v] for v in f)) for g in gs))]+=1
 for (b,f),n in out.items():yield b,f,n
def main():
 selected=set(sys.argv[1:]) or {f'{w}/{l}' for w in (11,12) for l in range(7,11)}
 assert selected<={f'{w}/{l}' for w in (11,12) for l in range(7,11)}
 with tempfile.TemporaryDirectory() as t:
  binary=Path(t)/'frontier'
  subprocess.run(['c++','-std=c++17','-O3',here/'frontier.cpp','-o',binary],check=True)
  for w in (11,12):
   for l in range(7,11):
    if f'{w}/{l}' not in selected:continue
    k=22-w-l;rows=list(domain(w,l))
    expected={(11,7):(3,27),(11,8):(150,2673),(11,9):(2604,55863),(11,10):(9938,223425),
              (12,7):(2,5),(12,8):(76,640),(12,9):(1409,24840),(12,10):(49990,1083735)}
    assert (len(rows),sum(n for _,_,n in rows))==expected[w,l]
    data=h+'\n'+f'{len(rows)} {w} {l} {k}\n'+''.join(' '.join(map(str,(*b,*f)))+'\n' for b,f,n in rows)
    r=subprocess.run([binary],input=data,text=True,stdout=subprocess.PIPE,check=True)
    empty=list(map(int,r.stdout.split()));assert len(empty)==len(rows) and max(empty)<=21
    print(w,l,k,len(rows),sum(n for b,f,n in rows),Counter(empty),flush=True)
if __name__=='__main__':main()

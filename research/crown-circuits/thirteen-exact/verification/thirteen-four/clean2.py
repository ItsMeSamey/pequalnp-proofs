"""Two private clean terminals; exhaust restrictions with optional mixed raw occurrences."""
from itertools import combinations,permutations
from functools import lru_cache
from collections import Counter
from pathlib import Path
def params(row):
 p,g,c,b,q,d=row
 es=[(1<<i)|(1<<j) for i in range(p) for j in range(i) if g>>(i*(i-1)//2+j)&1]
 extra=sum(([1<<i]*(3+(q>>i&1)-sum((x>>i)&1 for x in es)) for i in range(p)),[])
 extra += [0]*(13-len(es)-len(extra))
 return es,extra
def sortkey(tags,clean):
 # available first; private last
 ps=[i for i in range(4) if not(clean>>i&1)]; cs=[i for i in range(4) if clean>>i&1]
 return min(tuple(sorted((sum(((t>>k)&1)<<j for j,k in enumerate(a+b)) for t in tags),key=lambda t:-t.bit_count())) for a in permutations(ps) for b in permutations(cs))
@lru_cache(None)
def poss(tags):
 jobs=[(i,) for i in range(len(tags))]+list(combinations(range(len(tags)),2)); full=(1<<len(jobs))-1
 def tab(f):return sum(1<<j for j,idx in enumerate(jobs) if f(idx))
 target=tab(lambda s:len(s)==2)
 pure=[tab(lambda s:any(tags[i]>>k&1 for i in s)) for k in range(4)]
 inject=sum(([tab(lambda s,i=i:i in s)]*(2-t.bit_count()) for i,t in enumerate(tags)),[])
 def close(bank):
  t={0,full}
  for b in bank:t|={a&b for a in t}
  return t
 def final(terms):
  good=[0]
  for mask in [full,pure[2],pure[3]]:
   opts={mask&t for t in terms if mask&t&~target==0}
   good=list({a|b for a in good for b in opts})
  return target in good
 @lru_cache(None)
 def recur(terms,todo):
  if not todo:return final(terms)
  # terms already intersection-closed. Extend by OR-ing a user raw with any product.
  for inj in set(todo):
   nxt=list(todo);nxt.remove(inj)
   for z in {inj|a for a in terms}:
    if recur(tuple(sorted(set(terms)|{a&z for a in terms})),tuple(nxt)):return True
  return False
 return recur(tuple(sorted(close(pure[:2]))),tuple(sorted(inject)))
if __name__=='__main__':
 rows=[tuple(map(int,l.split())) for l in Path('rows').read_text().splitlines()]
 for row in rows:
  p,g,c,b,q,d=row
  if c.bit_count()!=2 or d:continue
  es,extras=params(row)
  # At least two distinct labels outside private groups => a third terminal.
  if sum(t&c==0 for t in es+extras)<2:continue
  solved=False
  for k in range(4):
   for sub in sorted(set(combinations(extras,k)),key=lambda x:(x.count(0),x)):
    if len(es)+k<2 or sum(2-x.bit_count() for x in sub)>3:continue
    key=sortkey(es+list(sub),c)
    if not poss(key):
     print('X',*row,'|',*key,flush=True);solved=True;break
   if solved:break
  if not solved:print('O',*row,flush=True)

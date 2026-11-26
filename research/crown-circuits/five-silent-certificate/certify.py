"""Exhaustive support lower bound for six partial words on three ordered ANDs.
Every candidate pair of words has at least one opposite pair of fixed coordinates.
A fixed 0/1 denotes a different hot operand. A * can be 00 or 11."""
from itertools import combinations,product
from collections import Counter
vs=list(product(range(2),repeat=3))
def ext(v):
 return {u for u in vs if all(x==2 or x==y for x,y in zip(v,u))}
words=[w for w in product((0,1,2),repeat=3) if w.count(2)<=1]
E={w:ext(w) for w in words}
def gen(start,used,chosen):
 if len(chosen)==6:yield tuple(chosen);return
 if 8-len(used)<6-len(chosen):return
 for j in range(start,len(words)):
  v=words[j]
  if used.isdisjoint(E[v]):yield from gen(j+1,used|E[v],chosen+[v])
# Known hot singleton support per physical operand: a coordinate on which
# a pair uniquely differs if prior ANDs all have a common cold operand.
# diag has one hot literal (choice unknown). Inequalities use minimal mass.
def candidates(P):
 def cold(x):return {1-x} if x<2 else ({0,1} if x==2 else set())
 # literal support forced from pair with unique separating coordinate provided
 # every earlier coordinate shares a cold operand; a wildcard may be 11.
 known=[[set() for b in (0,1)] for k in range(3)]
 for i,j in combinations(range(6),2):
  a,b=P[i],P[j]
  dif=[k for k in range(3) if max(a[k],b[k])<2 and a[k]!=b[k]]
  if len(dif)!=1:continue
  k=dif[0]
  if any(not cold(a[t]).intersection(cold(b[t])) for t in range(k)):continue
  known[k][a[k]].add(i);known[k][b[k]].add(j)
 # Every known root is nonraw if it contains both ports of even one label.
 # It is an actual OR if all previous ANDs are cold on at least one of the
 # two forced literals and a constant cannot account for all observations.
 def actual_or(k,b):
  hot={i for i,w in enumerate(P) if w[k] in (b,3)}
  return len(hot)>=2 and all({i for i,w in enumerate(P) if w[t]==3}!=hot for t in range(k))
 # Analyze each first-layer operand OR tree. For each distinct OR root
 # firing on a source known to be in this operand, prove it is external
 # via a hot singleton of the other A-side. Distinct such ORs need evidence
 # of different diagonal values; known cold/hot via fixed code.
 def rootvals(k,b):return [int(w[k]==b or w[k]==3) for w in P]
 def distinct(k,b,l,c):return any(x is not None and y is not None and x!=y for x,y in zip(rootvals(k,b),rootvals(l,c)))
 for t in range(3):
  for s in (0,1):
   bound=0
   for i,w in enumerate(P):
    if w[t] not in (s,3) or any(w[l]==3 for l in range(t)):continue
    copies=2 if i in known[t][s] else 1
    extroots=[]
    for k in range(3):
     if k==t or w[k]>=2:continue
     b=w[k]
     if i not in known[k][b]:continue
     if not actual_or(k,b):continue
     if any(s in cold(w[t]) and w[k] in (b,3) for w in P):
      extroots.append((k,b))
    e=int(bool(extroots))
    if len(extroots)==2 and distinct(*extroots[0],*extroots[1]):e=2
    bound+=copies*(2**e)
   if bound>8:return True
 return False
def removable(P):
 for t in range(3):
  hot={i for i,w in enumerate(P) if w[t]==3}
  if hot and all(any(P[i][k] not in (b,3) for i in hot)
                 for k in range(t+1,3) for b in (0,1)):
   return True
 return False

if __name__=='__main__':
 counts=Counter()
 for q in gen(0,set(),[]):
  loc=[(i,k) for i,w in enumerate(q) for k in range(3) if w[k]==2]
  for bits in product((2,3),repeat=len(loc)):
   P=[list(w) for w in q]
   for (i,k),v in zip(loc,bits):P[i][k]=v
   result='Kraft' if candidates(P) else 'removable' if removable(P) else 'open'
   counts[result]+=1
   if result!='Kraft':print(result,P)
 print('Profile counts:',dict(counts))
 assert counts=={'Kraft':338,'removable':2}

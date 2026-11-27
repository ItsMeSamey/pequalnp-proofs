"""Synthesize small witness lists per pair of raw input labels, preserving each Checked goal."""
from pathlib import Path
from collections import Counter
import re,itertools,sys
here=Path(__file__).resolve().parent
dst=Path(sys.argv[1])
eps=lambda e,l,r:(True,l,r,l and r,l or r)[e]
def sub(p,q):return (q[0]<0 or q[0]==p[0]) and all(not eps(p[1],l,r) or eps(q[1],l,r) for l,r in itertools.product([0,1],repeat=2))
def epval(p,w):return (p[0]<0 or bool((w>>(p[0]+2))&1)) and eps(p[1],w&1,w&2)
def vertex(z):return {'x.l':0,'x.r':1}.get(z,2+int(z[6:-1]) if z.startswith('(x.raw ') else 0)
for k in 'AB':
 s=(here.parent/f'official9822-lean/OR9822Tables{k}.lean').read_text()
 sections=[]
 pat=r'(private def witnessCode \(p q : Tiny I\) : Nat :=\n  match index p with\n(?:  \| \d+ => [^\n]*\n)+  \| _ => 0)'
 offset=0
 for m in re.finditer(pat,s):
  raw=[list(map(int,x.split(','))) for x in re.findall(r'#\[([\d,]+)\]',m[1])]
  n=len(raw)//5-1;ps=[(i,e) for i in range(-1,n) for e in range(5)]
  target_line=s[:m.start()].split('def target (x : Row I) : Bool :=\n')[-1].splitlines()[0]
  token=r'(x\.[lr]|\(x\.raw [0-9]+\))'
  edges=[(vertex(a),vertex(b)) for a,b in re.findall(token+r' && '+token,target_line)]
  assert edges
  target=lambda w:any((w>>a)&(w>>b)&1 for a,b in edges)
  edge='Checked target true' in s[m.end():].split('private theorem cert1')[0]
  def checks(p,q,v):
   i=v%n;w=v//n;b=w|(1<<(i+2))
   return (p[0]<0 and q[0]<0 or sub(p,q) or sub(q,p) or p[0]==q[0]==i or
    edge and {p,q}=={(i,0),(-1,3)} or
    (p[0]==i or q[0]==i) and target(w)!=target(b) and
     bool(epval(p,w) or epval(q,w))==bool(epval(p,b) or epval(q,b)))
  universe=sorted(set(sum(raw,[])))
  for pi,p in enumerate(ps):
   for qi,q in enumerate(ps):assert checks(p,q,raw[pi][qi]),(n,pi,qi,raw[pi][qi],edges)
  buckets=[];cost=[]
  for hi in range(n+1):
   for lo in range(hi+1):
    remaining={(p,q) for p in ps for q in ps if sorted((p[0]+1,q[0]+1))==[lo,hi]}
    tests={v:{x for x in remaining if checks(*x,v)} for v in universe}
    xs=[]
    while remaining:
     v=max(universe,key=lambda v:(len(tests[v]&remaining),-v))
     covered=tests[v]&remaining;assert covered
     xs.append(v);cost.extend([len(xs)]*len(covered));remaining-=covered
    buckets.append(xs)
  grid=','.join('['+','.join(map(str,x))+']' for x in buckets)
  tg=str(edge).lower()
  alt=f'''private def witnessChoices : Array (List Nat) := #[{grid}]
private def witnessCode (p q : Tiny I) : Nat :=
  let a := index p / 5
  let b := index q / 5
  let h := max a b
  let candidates := witnessChoices[h*(h+1)/2 + min a b]?.getD []
  (candidates.find? fun w => decide (Checked target {tg} p q
    ⟨w % {n},Nat.mod_lt _ (by decide)⟩ (low (w / {n})))).getD 0'''
  sections.extend([s[offset:m.start()],alt]);offset=m.end()
  print(k,n,len(universe),len(buckets),sum(map(len,buckets)),max(cost),round(sum(cost)/len(cost),2))
 sections.append(s[offset:]);out=''.join(sections)
 (dst/f'CoveredTheta{k}9822.lean').write_text(out)
 print(len(s.encode()),len(out.encode()))

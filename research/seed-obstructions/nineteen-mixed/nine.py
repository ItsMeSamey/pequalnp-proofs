from pathlib import Path
p=Path(__file__).resolve().parents[1]/'seventeen-mixed'/'line_basis.py'
ctx={'__file__':str(p)}
exec(p.read_text().split('visits=0')[0],ctx)
rels,init=ctx['rels'],ctx['init']
pack=init[:7];states=0;families=set()
def visit(slots):
 global states
 states+=1
 while True:
  if slots[7][0]>(127^slots[8][1]):return
  for x,y in slots[7:]:
   for i,(a,b) in enumerate(pack):
    if not a&~x and not b&~y and 127^y<slots[i][0]:return
  opts=[];guaranteed=0;possible=0
  for i,(x,y) in enumerate(slots):
   m=g=0
   for j,(a,b) in enumerate(rels):
    if a&y or b&x:continue
    m|=1<<j
    if not a&~x and not b&~y:g|=1<<j
   opts.append((m,g));guaranteed|=g;possible|=m
  if possible!=(1<<len(rels))-1:return
  force=[(0,0) for i in slots]
  for i,(m,g) in enumerate(opts):
   others_m=others_g=0
   for k,(mm,gg) in enumerate(opts):
    if k!=i:others_m|=mm;others_g|=gg
   priv=m&~others_g
   if not priv:return
   a=b=127
   for j,(ra,rb) in enumerate(rels):
    if priv>>j&1:a&=ra;b&=rb
   for j,(ra,rb) in enumerate(rels):
    if m>>j&1 and not others_m>>j&1:a|=ra;b|=rb
   force[i]=slots[i][0]|a,slots[i][1]|b
  if any(x&y for x,y in force):return
  if slots==force:break
  slots=force
 cand=[]
 for j,(a,b) in enumerate(rels):
  if guaranteed>>j&1:continue
  possible=[k for k,(m,g) in enumerate(opts) if m>>j&1]
  i=possible[0];x,y=slots[i];free=(a|b)&~(x|y)
  cand.append((len(possible),i,free&-free))
 if cand:_,i,bit=min(cand)
 else:
  for i,(x,y) in enumerate(slots):
   free=127&~(x|y)
   if free:bit=free&-free;break
  else:families.add(tuple(sorted(x for x,y in slots)));return
 x,y=slots[i]
 for alt in [(x|bit,y),(x,y|bit)]:t=slots[:];t[i]=alt;visit(t)
visit(pack+[(0,0)]*2)
from collections import Counter
print('states',states,'families',len(families),'composition',Counter((sum(x.bit_count()==1 for x in f),sum(x.bit_count()-1 for x in f)) for f in families))
for f in sorted(families):print(*f)

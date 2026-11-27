"""Independently verify every recorded witness on every physical source bank."""
from pathlib import Path
import sys, re, ast, hashlib, zipfile
sys.path.insert(0,'/workspace/scratch/threshold-assembly-review/or23')
from sample import samples
here=Path(__file__).parent
packet=here/'original-point-joint.zip'
assert hashlib.sha256(packet.read_bytes()).hexdigest()=='dc0e86380ff0fb355038f0e491b1a62d6ffcda9af53e760363982a49b64432f7'
raw,front,target=samples(Path('/workspace/scratch/threshold-assembly-review/or23/L-meta-18968.json'))
rows=[x&((1<<20)-1) for x in raw]
pos={i for i in range(676) if ((target&~front)>>i)&1}
neg={i for i in range(676) if not (target>>i)&1}
assert len(pos)==28 and len(neg)==624
with zipfile.ZipFile(packet) as z:
 lines=z.read(next(k for k in z.namelist() if k.endswith('joint-check.log'))).decode().splitlines()
qs=[2,8,16,32]
for line in lines:
 d=int(line.split()[1]); traced=ast.literal_eval(re.search(r'\] (\[\[.*?\]\]) remaining',line)[1])
 for bank,opts in [(0,()),(7,(129,)),(17,(4160,)),(115,(129,4160))]:
  def feature(x):return x|sum(bool(x&c)<<(20+j) for j,c in enumerate(opts))
  sm=(1<<20)-1
  for cut,p,n,w in traced:
   old=[feature(x&sm) for x in rows];sm &= ~cut
   new=[feature(x&sm) for x in rows]
   assert p in pos and n in neg and w in pos
   assert old[p]==feature(rows[p]) and new[w]==feature(rows[w])
   assert all(a&~b==0 for a,b in zip(new,old))
   nonzero=0
   for v in new:nonzero |= v
   assert old[p]&~old[n]&nonzero==0
  assert [v[0] for v in traced]==[1<<d]+qs
  keep=[o for o in opts if not o&(1<<d)]
  for o in set(opts)-set(keep):
   alias=o^(1<<d)
   assert alias.bit_count()==1 and all(bool(o&x&sm)==bool(alias&x&sm) for x in rows)
  returning={rows[i]^(1<<d) for i in pos if (rows[i]&(1<<d)) and not rows[i]&sum(qs)}
  tags=sum(returning);degree=len(returning)
  assert degree==(2 if d in (0,2,6) else 3)
  assert all(not(rows[i]&(1<<d) and rows[i]&tags) for i in neg)
  cost=(29 if len(keep)<2 else 28)+3-degree
  expected=(30 if d in (0,2,6) else 29)-int(bank==115 and d in (2,8,9,10,11))
  assert cost==expected
print('36 bank/point combinations: 180 nested witness steps; all aliases, restoration terms and coefficients agree')

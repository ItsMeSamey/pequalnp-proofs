"""Check each positive pin against the literal body of the public floor theorem."""
from hashlib import sha256
from pathlib import Path
import re
from itertools import permutations
graph=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
p=Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_982.lean')
s=p.read_text().rsplit('theorem PEqualNP.Outside.L_meta_982 :',1)[1].split(':=',1)[0]
print(p.name,sha256(p.read_bytes()).hexdigest())
forms=re.findall(r'HasCircuitSize 7 \(fun x : Fin 7 → Bool => (.*?)\) t → (\d+) ≤ t',s)
for i in range(4):
 ns={b if a==i else a for a,b in graph if i in (a,b)}
 rem=sorted(set(range(10))-ns-{i})
 ed={tuple(sorted((a,b))) for a,b in graph if a in rem and b in rem}
 found=False
 for expr,count in forms:
  ref={tuple(sorted((int(a),int(b)))) for a,b in re.findall(r'x (\d+) && x (\d+)',expr)}
  if len(ed)!=len(ref):continue
  for perm in permutations(range(7)):
   mp=dict(zip(rem,perm))
   if {tuple(sorted((mp[a],mp[b]))) for a,b in ed}!=ref:continue
   for mask in range(1024):
    if not(mask>>i&1):continue
    raw=lambda v:bool(mask>>v&1)
    small=sum(raw(v)<<j for v,j in mp.items())
    pred=any(small>>a&small>>b&1 for a,b in ref)
    assert any(raw(a) and raw(b) for a,b in graph)==(any(raw(a) for a in ns) or pred)
   print('pin',i,'neighbors',sorted(ns),'map',mp,'7-floor',count,'9-floor',int(count)+2)
   found=True;break
  if found:break
 assert found

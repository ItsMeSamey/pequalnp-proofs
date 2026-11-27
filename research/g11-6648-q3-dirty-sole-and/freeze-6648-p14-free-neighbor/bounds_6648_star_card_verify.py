from pathlib import Path
import re, subprocess
repo=Path('/workspace/pequalnp-proofs')
source=(repo/'lean/PEqualNP/Outside/L_meta_6648.lean').read_text()
edges={tuple(map(int,p)) for p in re.findall(r'\(\((\d+) : ℕ\), \((\d+) : ℕ\)\)',source)}
assert len(edges)==16
cases=[(8481,[8,1,4,5,2,3,6,7]),(8459,[6,7,3,10,9,0,2,5]),(8511,[8,1,4,9,7,0,3,6]),(8399,[8,9,5,4,1,0,2,10]),(982,[7,3,6,9,5,0,2]),(982,[6,3,7,10,4,0,1]),(982,[8,5,9,1,4,2,0]),(982,[4,8,1,10,5,2,0]),(927,[6,3,7,10,0,2]),(927,[10,4,6,2,1,3]),(927,[9,8,5,7,1,3])]
floors=[]
for a,(n,m) in enumerate(cases):
 src=subprocess.check_output(['git','-C',str(repo),'show',f'upstream/main:lean/PEqualNP/Outside/L_meta_{n}.lean'],text=True)
 decl=src[src.rfind('theorem PEqualNP.Outside.'):]; neighbors={v for e in edges if a in e for v in e if v!=a}; core={e for e in edges if not set(e)&(neighbors|{a})}; hits=[]
 for i,(arity,expr,k) in enumerate(re.findall(r'HasCircuitSize (\d+) \(fun x : Fin \d+ → Bool => (.*?)\) t → (\d+) ≤ t',decl)):
  if int(arity)!=len(m):continue
  pairs=[tuple(map(int,p)) for p in re.findall(r'x (\d+) && x (\d+)',expr)]
  if {tuple(sorted((m[u],m[v]))) for u,v in pairs}==core:hits.append((i+1,int(k)))
 assert hits,(a,n); floor=max(k for i,k in hits)+len(neighbors);floors.append(floor);print(a,n,hits,floor)
assert floors==[14,16,15,17,13,13,14,14,12,11,12]
assert not any(max(floors[a],floors[b])<=11 for a,b in edges)

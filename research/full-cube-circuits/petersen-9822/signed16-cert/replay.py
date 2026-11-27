"""Replay the independent allocation censuses and directly test the upper witness."""
from pathlib import Path
import json, subprocess, sys, hashlib
root=Path(__file__).resolve().parent
for line in (root/'SHA256SUMS').read_text().splitlines():
 h,name=line.split(maxsplit=1)
 if hashlib.sha256((root/name).read_bytes()).hexdigest()!=h:raise SystemExit('hash mismatch: '+name)
def run(name,dir):
 q=subprocess.run([sys.executable,'-B',name],cwd=root/dir,capture_output=True,text=True,check=True)
 return q.stdout
tests=[('truth_replay.py','reductions','truth_replay.log'),('four_bins.py','reductions','four_bins.log'),('audit_guard.py','reductions','audit_guard.log')]
for file,d,log in tests:
 assert run(file,d)==(root/d/log).read_text(),file
 print(file,'matched')
for f in ['audit-three.py','audit-four.py']:print(run(f,'verification').strip())
gates=json.loads((root/'calculus/upper18.json').read_text())
assert len(gates)==18
edges=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
for x in range(1024):
 w=[bool(x>>i&1) for i in range(10)]
 for op,a,b in gates:
  assert op in ('and','or') and 0<=a<len(w) and 0<=b<len(w)
  w.append(w[a] and w[b] if op=='and' else w[a] or w[b])
 assert w[-1]==any(w[a] and w[b] for a,b in edges)
print('18 AND/OR gates; all 1024 full-cube assignments agree')

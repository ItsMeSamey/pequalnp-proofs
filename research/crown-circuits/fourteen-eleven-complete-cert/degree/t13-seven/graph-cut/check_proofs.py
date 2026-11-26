from pathlib import Path
import hashlib,subprocess
from cert import check
rows={}; 
for line in Path('query.out').read_text().splitlines():
 i,p,g,r,s=map(int,line.split())
 if s==0:rows[(p,g)]=max(r,rows.get((p,g),-1))
for (p,g),r in sorted(rows.items()):
 assert r>=0 and not check(p,g,r)
 name=f'cert-{p}-{g}'
 paths=[Path(name+ext) for ext in ['.cnf','.drat']]
 res=subprocess.run(['/workspace/scratch/syn_pruning/bank11/drat-trim',*map(str,paths)],capture_output=True,check=True)
 assert b's VERIFIED' in res.stdout
 print(p,g,r,*(hashlib.sha256(x.read_bytes()).hexdigest() for x in paths),flush=True)
 for x in paths:x.unlink()

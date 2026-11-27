from pathlib import Path as P
import json,re,hashlib
base=P('/workspace/scratch')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
known={}
for s in ['review-q401','review-q401-increment','review-q401-plus2','review-q401-batches','review-q401-pinrun']:
 d=base/s; f=P((d/'workdir').read_text().strip())/'fresh'
 rows=json.loads((d/'ledger.json').read_text()) if s.endswith(('batches','pinrun')) else json.loads((d/'receipt.json').read_text())['modules']
 for n,r in rows.items():
  n=n.removesuffix('.lean');o=f/(n+'.olean');assert sha(o)==r['object']
  known[n]=str(o)
dirs=[base/d for d in ('incidence-warm-traces','incidence-q401','incidence-weighted-plane','incidence-witnesses','incidence-hoist','incidence-pin-hoist','incidence-run-pin','incidence-release-check')]+[base]
new={}
def visit(n):
 if n in known or n in new:return
 p=next(d/(n+'.lean') for d in dirs if (d/(n+'.lean')).is_file() and not (d.name=='incidence-warm-traces' and n=='IncidencePointCutSet'))
 deps=re.findall(r'^import ((?:Protected|Incidence|Hoist)[\w.]*)',p.read_text(),re.M)
 for j in deps:visit(j)
 new[n]=dict(source=str(p),sha=sha(p),imports=deps)
visit('IncidenceWarmActualPointCap')
if __name__=='__main__':print(json.dumps(new,indent=2))

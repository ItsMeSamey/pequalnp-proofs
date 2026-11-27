from pathlib import Path as P
import hashlib,json,re
d=P(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((d/'ledger.json').read_text())
assert len(r)==29
ax={}
for n,v in r.items():
 z=(d/(n+'.log')).read_text()
 for name,ls in re.findall(r"'([\w.']+)' depends on axioms: \[([^\]]*)\]",z):
  arr=sorted(ls.split(', '));assert set(arr)<={'propext','Classical.choice','Quot.sound','choice'},(name,arr);ax[name]=arr
 assert 'sorryAx' not in z
for n in ('IncidencePinRunBound.bound','IncidenceWeightedPlane.bound','IncidenceWeightedEdits.edit_cap','IncidencePostHoistPinExpectation.expected'):assert n in ax
(d/'axioms.json').write_text(json.dumps(ax,indent=2)+'\n')
(d/'receipt.json').write_text(json.dumps(dict(counts={s:sum(v['stage']==s for v in r.values()) for s in ['pin-hoist','run-pin','weighted-plane']},ledger=sha(d/'ledger.json'),axioms=sha(d/'axioms.json'),public_reports=len(ax),lean='4.36.0',input_locks='replay.py',replay=sha(d/'replay.py')),indent=2)+'\n')
print(sha(d/'receipt.json'),len(ax))
import subprocess
for st,commit,m,h in [
 ('pin-hoist','f07b3ab79fa8de3da5de7f3ba1e64fb72cdaa09d','release.sha256','e79ebda52c20e9a157799d8e5302e467b39537881e15d4bc0c7c8ccc115f196a'),
 ('run-pin','a422c1cd07e0b85996ae5fe6791b82aafc1a4eb3','run-pin-manifest.json',None),
 ('weighted-plane','306e19b80026cdf69b98a3df8737da17feb11846','weighted-plane-manifest.json',None)]:
 b=subprocess.check_output(['git','-C','/workspace/pnp-research','show',commit+':research/incidence-witnesses/physical-lean/'+st+'/'+m])
 if h:
  assert hashlib.sha256(b).hexdigest()==h
  hashes={k:v for v,k in (x.split() for x in b.decode().splitlines())}
 else:
  data=json.loads(b);hashes=data.get('files',{}).copy()
  for row in data['modules']:hashes.update(row.get('sha256',{}))
 for n,row in r.items():
  if row['stage']==st:assert row['log']==hashes['receipts/'+n+'.log']

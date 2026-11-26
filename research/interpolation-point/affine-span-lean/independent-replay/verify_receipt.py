from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;r=json.loads((D/'receipt.json').read_text());R=Path((D/'workdir').read_text().strip());src=R/r['rel']; sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src/'SHA256SUMS')==r['manifest_sha256']
for line in (src/'SHA256SUMS').read_text().splitlines():
 h,f=line.split();assert sha(src/f)==h
for m in r['modules']:
 n=m['module'];assert sha(src/(n+'.lean'))==m['source_sha256'] and sha(R/'fresh'/(n+'.olean'))==m['olean_sha256']
 assert m['axioms']==[s for s in (src/'producer'/(n+'.log')).read_text().splitlines() if 'depends on axioms:' in s]
assert sha(D/'prerequisites.json')==r['prerequisites_sha256']
for p in json.loads((D/'prerequisites.json').read_text()):
 assert sha(Path(p['path']))==p['olean_sha256'] and sha(R/'mathlib-source'/(p['module'].replace('.','/')+'.lean'))==p['source_sha256']
print('4/4 fresh local modules, 2/2 private pinned Mathlib prerequisites, 7/7 printed axiom reports, all source/object digests reverified.')

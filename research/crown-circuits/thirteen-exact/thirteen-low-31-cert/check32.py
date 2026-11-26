import json
from pathlib import Path
r=json.loads(Path(__file__).with_name('size32.json').read_text())
for assn in range(8192):
 w=[bool(assn & (1<<i)) for i in range(13)]
 for op,a,b in r['gates']:
  assert op in ('OR','AND') and max(a,b)<len(w)
  w.append(w[a] or w[b] if op=='OR' else w[a] and w[b])
 assert w[r['output']]==(assn.bit_count()>=2)
assert len(r['gates'])==32 and sum(g[0]=='AND' for g in r['gates'])==5
print('32 gates, five ANDs, all 8192 assignments checked individually')

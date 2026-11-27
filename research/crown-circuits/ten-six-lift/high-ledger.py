from collections import Counter
from pathlib import Path
import gzip,sys,io
depth=int(sys.argv[1]);p=Path(__file__).parent
orb=Path('/dev/shm')/f'duality-t8-orbits-{depth}.tsv'
catalog={tuple(map(int,r.split()[:depth])):tuple(map(int,r.split()[depth:])) for r in orb.read_text().splitlines()}
files=list(p.glob(f'high-{depth}-*-*.log'))
if depth==4:files.append(p/'four-fixed-pilot.log')
keys={};summary=Counter()
for f in files:
 for line in f.read_text().splitlines():
  fields=line.split()
  if not fields:continue
  key=tuple(map(int,fields[:depth]));assert key in catalog and key not in keys
  assert fields[depth:depth+4]==['valid','1','hit','0']
  keys[key]=tuple(map(int,(fields[-3],fields[-1])))
with gzip.GzipFile(filename=str(p/f't8-{depth}-profile-ledger.tsv.gz'),mode='wb',mtime=0) as packed, io.TextIOWrapper(packed,encoding='utf-8',newline='\n') as dst:
 print('targets cost orbit-size status nodes fronts',file=dst)
 for key,(cost,count) in catalog.items():
  stats=keys.get(key)
  print(*key,cost,count,'exact' if stats else 'open',*(stats if stats else (0,0)),file=dst)
  summary[cost,bool(stats)]+=1
print(depth,sorted(summary.items()),'completed-chronological',sum(catalog[k][1] for k in keys),'nodes/fronts',tuple(map(sum,zip(*keys.values()))))

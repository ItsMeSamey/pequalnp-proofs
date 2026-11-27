import runpy
from pathlib import Path
from collections import Counter
p=Path(__file__).parent;canon=runpy.run_path(str(p/'dirty-permute.py'))['canon']
rows={};other=Counter()
for f in sorted(p.glob('three-exact-*-*.log')):
 for line in f.read_text().splitlines():
  r=line.split()
  if len(r)<11 or r[3:7]!=['valid','1','hit','0']:raise ValueError((f,line))
  key=tuple(map(int,r[:3]));assert key not in rows
  rows[key]=(int(r[-3]),int(r[-1]))
T=[tuple(map(int,l.split())) for l in (p/'t8-three-mandatory.tsv').read_text().splitlines()]
alias={canon(t[:3]):t[:3] for t in T if t[3]==0 and t[:3] in rows};ledger=[]
for a,b,c,cost in T:
 key=a,b,c
 if key in rows:msg='exact',*key,*rows[key]
 elif cost==0 and canon(key) in alias:msg='permutation',*alias[canon(key)],0,0
 else:msg='open',0,0,0,0,0
 other[msg[0]]+=1;ledger.append((a,b,c,cost,*msg))
print(other,'exact nodes/fronts',tuple(map(sum,zip(*rows.values()))))
(p/'t8-three-exact-ledger.tsv').write_text('T0\tT1\tT2\tcost\tstatus\trep0\trep1\trep2\tnodes\tfronts\n'+''.join('\t'.join(map(str,row))+'\n' for row in ledger))

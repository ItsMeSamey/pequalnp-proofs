from collections import Counter
from pathlib import Path
d=Path(__file__).parent
ref=Path('/workspace/scratch/crown18264/verification/threshold-eight/eight-ledger.txt')
expected={i:(cap,flag) for i,_,cap,_,flag in (map(int,s.split()[:5]) for s in ref.read_text().splitlines())}
got={}
for p in sorted(d.glob('run[0-7].txt')):
 for s in p.read_text().splitlines():
  row=s.split()
  if len(row)!=4:continue
  i,cap,visited,flag=map(int,row)
  assert i not in got and visited>0
  got[i]=cap,flag
mis=[(i,got[i],expected[i]) for i in got if expected[i]!=got[i]]
print('IDs',len(got),'target',len(expected),'survivors',sum(v[1] for v in got.values()),'expect',sum(v[1] for v in expected.values()),'incorrect',len(mis),mis[:3])
if len(got)==25721:
 assert not mis and len(expected)==25721 and sum(v[1] for v in got.values())==797
 print('PASS',sorted(Counter(got.values()).items()))

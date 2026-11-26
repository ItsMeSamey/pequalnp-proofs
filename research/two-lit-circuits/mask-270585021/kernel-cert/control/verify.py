import json,sys
from pathlib import Path
gates=json.loads(Path(sys.argv[1]).read_text())
assert len(gates)<=int(sys.argv[2])
mask=0
for i in range(6):
 for j in range(6):
  wires=[k==i or k==j for k in range(6)]
  for op,*args in gates:
   assert op in ('or','and','not') and len(args)==(1 if op=='not' else 2)
   assert all(0<=a<len(wires) for a in args)
   t=[wires[a] for a in args]
   wires.append(any(t) if op=='or' else all(t) if op=='and' else not t[0])
  bit=6*min(i,j)+max(i,j)
  assert wires[-1]==bool(270585021>>bit&1),(i,j)
  mask|=int(wires[-1])<<bit
print(len(gates),'gates, 36/36 ordered pairs, mask',mask)

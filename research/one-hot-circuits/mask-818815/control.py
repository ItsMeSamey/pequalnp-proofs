from pathlib import Path
import json
gates=[["or",7,8],["or",10,9],["and",1,11],["or",2,3],["and",13,5],["and",2,6],["or",12,14],["or",16,15],["or",0,4],["or",18,17]]
mask=0
for u in range(4):
    for v in range(6):
        wires=[i==u for i in range(4)]+[i==v for i in range(6)]
        for op,a,b in gates:
            assert a<len(wires) and b<len(wires)
            wires.append((wires[a] and wires[b]) if op=='and' else (wires[a] or wires[b]))
        mask|=int(wires[-1])<<(6*u+v)
assert mask==818815
Path('baseline10.json').write_text(json.dumps(gates)+'\n')
print(len(gates),mask,'24/24')

from independent import ledger
from pathlib import Path
import hashlib, re
src=Path(__file__).parent
table=ledger();seen=set();runs=0
for file in [src/'first-replay.log',*sorted((src/'batches').glob('*.keys'))]:
    runs+=1
    for line in file.read_text().splitlines():
        stamp,t,idx,b,z,count,duration,h=line.split()
        t,idx,b,z,count=map(int,(t,idx,b,z,count))
        assert table[t][idx]==(t,b,z) and count==0 and (t,idx) not in seen
        assert h==hashlib.sha256(repr((t,idx,b,z,[])).encode()).hexdigest()
        seen.add((t,idx))
need={(t,i) for t,T in enumerate(table) for i in T}
assert seen==need,(len(seen),len(need))
print('Matching fresh results:',len(seen),'in',runs,'stages')
print('Samples by label:',*[len(T) for T in table])
print('Filter-set cases:',len(seen)*29)
print('Ordered fresh result digest:',hashlib.sha256(repr(sorted((t,idx,table[t][idx],0) for t,idx in seen)).encode()).hexdigest())

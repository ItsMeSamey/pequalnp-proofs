from pathlib import Path
import json,sys,hashlib
src=Path(sys.argv[1])
assert hashlib.sha256(src.read_bytes()).hexdigest()=='07f61656beb4d9bf2930c6b2029ef2297d5b1643e98dbba33eecc7abcfab8d60'
d=json.loads(src.read_text())
def span(cols):
 s={0}
 for x in cols:s.update(y^x for y in list(s))
 return s
def exact(row,ids):return span([row['columns'][i] for i in ids])&span(row['names'])=={0,row['names'][0]}
def supports(row):
 return [ids for m in range(1<<len(row['columns'])) if set(row['forced'])<=(ids:={i for i in range(len(row['columns'])) if m>>i&1}) and exact(row,ids)]
a,b,q=d['no'],d['yes'],d['quotient'];f=lambda x:x^(3 if x&2 else 0)
assert (f(1),1^3)==(1,2) and list(map(f,a['names']))==q['names']==[1,4,8]
assert list(map(f,a['columns'][1:]))==q['columns'] and f(a['columns'][0])==0
assert a['certificate']==q['certificate']
assert [t['interface'] for t in a['certificate']['steps']]==[[],[4],[4,8]]
assert supports(a)==[] and supports(b)==[set(b['support'])]==[{0,1,2}]
for m in range(256):
 ids={i for i in range(8) if m>>i&1}
 assert exact(q,ids)==exact(a,{0}|{i+1 for i in ids})
print('256 optional selections checked on raw and quotient IDs; NO. Positive original support {0,1,2}. MSB and LSB controls 1 and 2. Three interfaces [], [4], [4,8].')

from pathlib import Path
import json,re,zipfile

archive=Path('/workspace/scratch/synthesis_new/hard4-lost-read.zip')
with zipfile.ZipFile(archive) as z:
    official=json.loads(z.read('L-meta-18968.json'))['formal_statement']
    originals=[json.loads(l) for l in z.read('remaining.jsonl').splitlines()]
seeds=[int(''.join(v.zfill(19) for v in re.findall(r'\((\d+) : ℕ\)',block))) for block in re.findall(r'\[([^]]+)\]',official)]
outputs={int(i):int(v) for i,v in re.findall(r'x1 \((\d+) : ℕ\) = \((\d+) : ℕ\)',official)}
rows=[]
point_fields=[1<<i for i in range(13)]
def decode(i,seed,offset,width):
    return sum(((seed>>(i-i%13+(i-j-offset)%13))&1)<<j for j in range(width))
for i in range(676):
    status=1 if (outputs[88]&~outputs[54])>>i&1 else (-1 if not outputs[88]>>i&1 else 0)
    rows.append((decode(i,seeds[0],0,13),decode(i,seeds[1],6,7),status))
degree={p:sum(t for pt,t,s in rows if s==1 and pt==p) for p in point_fields}
D=sum(p for p,u in degree.items() if u.bit_count()==1)
O=8191-D
def state(p,t,mask):
    return (p&mask)|(t<<13)|(int(bool(p&129))<<20)|(int(bool(p&4160))<<21)
count=0
for id_,t,E,R,C in originals:
    if id_ not in {4243,6184,8204,10224}:continue
    assert t==1 and len(E)==1 and R==8191-E[0] and C==[129,4160]
    for q,u in degree.items():
        if not(D&q&R):continue
        src=state(q,u,R)
        assert src==q|u<<13 and sum((p,t,s)==(q,u,1) for p,t,s in rows)==1
        nn=[(p,t) for p,t,s in rows if s==-1]
        qneg=[(p,t) for p,t in nn if p&q]
        assert len(qneg)==168 and all(not (t&u) and state(p,t,R)&src==q for p,t in qneg)
        for c in C:
            assert any((p&c) and (t&u) and not (p&q) for p,t in nn)
        P={state(p,t,O) for p,t,s in rows if s==1 and p&O and t!=u}
        N={state(p&O,t&~u,O) for p,t in qneg}
        assert len(P)==21 and len(N)==90
        ordinary=[p for p in point_fields if p&O]+[1<<(j+13) for j in range(7) if 1<<j!=u]
        assert all(any((x&~y)==v for x in P for y in N) for v in ordinary)
        print(id_,q,u.bit_length()-1,len(P),len(N))
        count+=1
assert count==12

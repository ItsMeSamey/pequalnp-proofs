"""Validate all h3 clique hints by conservative rectangle coverage without a clique solver."""
from pathlib import Path
import argparse,struct,zlib,hashlib
from functools import lru_cache
from itertools import combinations
here=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('cert',type=Path)
parser.add_argument('--pack',type=Path)
args=parser.parse_args()
edges=[6,24,17,33,66,132,264,528,160,640,576,320,288]
inside=[sum(1<<j for j,e in enumerate(edges) if (x&e)==e) for x in range(1024)]
MIS=[x for x in range(1024) if not inside[x] and all(inside[x|(1<<j)] for j in range(10) if not(x>>j)&1)]
assert len(MIS)==16
raw=[sum(1<<j for j,e in enumerate(edges) if x&e) | (sum(1<<j for j,m in enumerate(MIS) if x&m)<<13) for x in range(1024)]
allE=(1<<13)-1
def hidden(q):
    return q>>13!=0 and all((q&allE)&~raw[1<<i] for i in range(10))
shores=set()
for a in range(1,1024):
    b=1023^a
    while b:
        if b<a and hidden(h:=raw[a]&raw[b]):shores.add(h)
        b=(b-1)&(1023^a)
assert len(shores)==13732
cross={(i,j):inside[MIS[i]|MIS[j]] for i,j in combinations(range(16),2)}
@lru_cache(None)
def no_fourteen(pairs):
    return not any(all(((1<<i)|(1<<j))&p for p in pairs) for i,j in combinations(range(16),2))
def first(h):
    e=h&allE;n=h>>13
    pairs=tuple((1<<i)|(1<<j) for (i,j),d in cross.items() if d&~e==0 and n&((1<<i)|(1<<j))==0)
    return no_fourteen(pairs)
roots=sorted(h for h in shores if first(h))
assert len(roots)==335
if args.pack:
    parts=[b'H3R1',struct.pack('<H',len(roots))]
    for index,h in enumerate(roots):
        parts.append(struct.pack('<I',h))
        for mode in [0,1]:
            b=(args.pack/f'{mode}-{index:03}.bin').read_bytes()
            assert len(b)%2==0
            parts.extend([struct.pack('<H',len(b)//2),b])
    args.cert.write_bytes(zlib.compress(b''.join(parts),9))
blob=zlib.decompress(args.cert.read_bytes())
assert blob[:4]==b'H3R1' and struct.unpack_from('<H',blob,4)[0]==335
pos=6
exceptions={(786481,q) for q in [5047856,788144,26106200,788016,26106184,26106216]}|{(26106184,786481)}
admitted=set()
nodecnt=[0,0];hintcnt=[0,0]
for index,H in enumerate(roots):
    assert struct.unpack_from('<I',blob,pos)[0]==H;pos+=4
    hp=H&allE;hn=H>>13
    for nested in [0,1]:
        count=struct.unpack_from('<H',blob,pos)[0];pos+=2
        hints=struct.unpack_from(f'<{count}H',blob,pos);pos+=2*count
        cursor=0;seen=set();attach=H if nested else 0
        def accept(A,B):
            global cursor
            if not nested and A>B:A,B=B,A
            state=(A,B)
            if state in seen:return
            seen.add(state);nodecnt[nested]+=1
            upper=(raw[A]|attach)&raw[B]
            if not hidden(upper):return
            mask=hints[cursor];cursor+=1
            if not mask:
                overlap=A&B
                if overlap:
                    bit=overlap&-overlap
                    accept(A^bit,B);accept(A,B^bit)
                    return
                assert upper==H or (H,upper) in exceptions,(index,nested,A,B,upper)
                if upper!=H:admitted.add((H,upper))
                for x in range(10):
                    if A>>x&1:accept(A^(1<<x),B)
                for x in range(10):
                    if B>>x&1:accept(A,B^(1<<x))
                return
            assert mask.bit_count()==8
            ns=[i for i in range(16) if mask>>i&1]
            candidates=[]
            for i,j in combinations(ns,2):
                pair=(1<<i)|(1<<j)
                required=cross[i,j]&~(0 if hn&pair else hp)
                assert required
                if required&~upper:continue
                assert (upper>>13)&pair
                for sides in range(4):
                    if nested and (((sides&1) and hn>>i&1) or ((sides&2) and hn>>j&1)):continue
                    A2=A&~((MIS[i] if sides&1 else 0)|(MIS[j] if sides&2 else 0))
                    B2=B&~((0 if sides&1 else MIS[i])|(0 if sides&2 else MIS[j]))
                    maximal=(raw[A2]|attach)&raw[B2]
                    if required&~maximal or not hidden(maximal):continue
                    assert (A2,B2)!=(A,B) and maximal>>13&pair==0
                    if (A2,B2) not in candidates:candidates.append((A2,B2))
            for a,b in candidates:
                if not any((a,b)!=(c,d) and a&~c==0 and b&~d==0 for c,d in candidates):
                    accept(a,b)
        accept(1023,1023)
        assert cursor==count,(index,nested,cursor,count)
        hintcnt[nested]+=count
assert pos==len(blob) and admitted==exceptions
print('roots',len(roots),'modes',2,'states',nodecnt,'hints',hintcnt,'exceptions',len(admitted),'bytes',args.cert.stat().st_size,'sha256',hashlib.sha256(args.cert.read_bytes()).hexdigest())

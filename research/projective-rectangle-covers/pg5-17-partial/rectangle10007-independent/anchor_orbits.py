"""Safe large-rectangle anchors up to verified projective collineations."""
from collections import deque
from itertools import combinations
from pathlib import Path
import json

root=Path(__file__).resolve().parent
rows=json.loads((root.parent/'official10007'/'reductions'/'rows.json').read_text())
n=31
full=(1<<n)-1

def bits(mask):
    while mask:
        bit=mask & -mask
        yield bit.bit_length()-1
        mask ^= bit

def closure(left):
    right=full
    for i in bits(left):
        right &= ~rows[i]
    return sum(1<<i for i,row in enumerate(rows) if not row & right),right

def norm(p):
    inv=pow(next(x for x in p if x),-1,5)
    return tuple(x*inv%5 for x in p)

# Multiply by T in F5[T]/(T^3+T+1).
powers=[]
a,b,c=1,0,0
for _ in range(n):
    powers.append(norm((a,b,c)))
    a,b,c=-c%5,(a-c)%5,b
assert len(set(powers))==n
for u in range(1,n):
    pts=[powers[(u*i)%n] for i in range(n)]
    lines=[sum(1<<i for i,p in enumerate(pts) if sum(x*y for x,y in zip(p,l))%5==0) for l in powers]
    official=[sum(1<<i for i in range(n) if rows[i]>>j&1) for j in range(n)]
    if set(lines)==set(official):break
else:raise AssertionError('coordinate identification failed')
point_id={p:i for i,p in enumerate(pts)}
maps=[lambda x,y,z:(y,z,x),lambda x,y,z:(y,x,z),lambda x,y,z:((x+y)%5,y,z),lambda x,y,z:(2*x%5,y,z)]
tables=[]
for f in maps:
    perm=[1<<point_id[norm(f(*p))] for p in pts]
    def apply(mask):return sum(perm[i] for i in bits(mask))
    assert {apply(l) for l in lines}==set(official)
    tables.append([[apply((m<<(8*j))&full) for m in range(256)] for j in range(4)])
frame=sum(1<<point_id[p] for p in [(1,0,0),(0,1,0),(0,0,1),(1,1,1)])
line=lines[0]
outside=next(bits(full^line))
candidates=set()
def add(left):
    if left:
        closed,right=closure(left)
        a,b=left.bit_count(),right.bit_count()
        if closed==left and a<=b and a*b>=46:candidates.add(left)
for k in range(5):
    for t in combinations(bits(full^frame),k):add(frame|sum(1<<x for x in t))
sub=line
while True:
    add(sub);add(sub|(1<<outside))
    if not sub:break
    sub=(sub-1)&line
print('Singer exponent',u,'normalized seeds',len(candidates),flush=True)
reps=[]
while candidates:
    seed=min(candidates);seen={seed};queue=deque([seed])
    while queue:
        x=queue.popleft();a,b,c,d=x&255,(x>>8)&255,(x>>16)&255,x>>24
        for t0,t1,t2,t3 in tables:
            y=t0[a]|t1[b]|t2[c]|t3[d]
            if y not in seen:
                seen.add(y);queue.append(y)
    candidates.difference_update(seen)
    r=min(seen);_,c=closure(r)
    reps.append((r.bit_count(),c.bit_count(),r,c,len(seen)))
for row in sorted(reps):print(*row)
print('orbits',len(reps),'narrow large rectangles',sum(x[4] for x in reps))

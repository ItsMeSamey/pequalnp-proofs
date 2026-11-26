"""Chronological normalized three-dirty four-terminal continuation templates."""
from itertools import product,combinations_with_replacement
from collections import Counter

def flip(x):
    return (x>>1)|((x&1)<<1)
types=[q for q in product(range(3),repeat=3) if q<=tuple(map(flip,q))]
connections=[q for q in product(range(4),repeat=2) if q<=tuple(map(flip,q))]

def minimum_unions(masks):
    """Exact for up to three distinct outputs by transpose to at most three inputs."""
    d=tuple(sorted(set(masks)))
    incidence={sum((1<<j) for j,k in enumerate(d) if k>>i&1) for i in range(14)}-{0}
    required={k for k in incidence if k.bit_count()>1}
    additional=int(7 in required and not required&{3,5,6})
    return (int.bit_count(d[0]|d[-1]|(d[1] if len(d)==3 else 0))-len(d)+len(required)+additional)

def templates():
    for columns in combinations_with_replacement(types,4):
        terminal=[sum(col[i]<<(2*(j+3)) for j,col in enumerate(columns)) for i in range(3)]
        for first in (0,1,3):
            for a,b in connections:
                T=[terminal[0]|(first<<2)|(a<<4),terminal[1]|(b<<4),terminal[2]]
                if not all(T):continue
                valid=True
                for start,x in enumerate(T):
                    for j in range(start+1,3):
                        if x>>(2*j)&3==3:x|=T[j]
                    if x&(x>>1)&0x1540:valid=False;break
                if valid:yield tuple(T)

if __name__=='__main__':
    counts=Counter()
    for t in templates():counts[t[0].bit_count(),minimum_unions(t)]+=1
    for (w,h),n in sorted(counts.items()):print(w,h,n)

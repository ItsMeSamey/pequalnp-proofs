"""Raw ordinary PC closure on two pinned copies with an odd disagreement marker."""
from pathlib import Path
import runpy
from collections import deque
from functools import lru_cache
from itertools import combinations_with_replacement
pkg=Path(__file__).parent
raw=runpy.run_path(str(pkg/'rooted-gap.py'))
g=raw['EXAMPLE']
def check(d):
    n=24;G=g+[a<<12 for a in g]
    pos,low,mul=raw['ring'](n,d);bas={};todo=deque()
    for i,row in enumerate(G):
        todo.append((1<<pos[(i,)])^(1<<pos[(i,i)]))
        todo.append(sum(1<<pos[tuple(sorted((i,j)))] for j in range(n) if row>>j&1))
    for i in (0,1,12,13):todo.append(1^(1<<pos[(i,)]))
    todo.append(1^(1<<pos[(2,)])^(1<<pos[(14,)]))
    while todo:
        p=raw['reduce'](todo.popleft(),bas)
        if not p:continue
        if p==1:return True,len(bas)+1
        k=p.bit_length();bas[k]=p
        if k<=low:
            support=[]
            while p:
                bit=p&-p;p^=bit;support.append(bit.bit_length()-1)
            for mx in mul:
                z=0
                for j in support:z^=mx[j]
                todo.append(z)
    return False,len(bas)
if __name__=='__main__':
    for d in [2,3]:print(d,check(d),flush=True)
    path=[8,10,9,7,5,4,4,2,8,10,11,10,7,2,3,2,6]
    def lc(G,j):
        old=G[j]
        return [row^(old^(1<<i)) if old>>i&1 else row for i,row in enumerate(G)]
    for encoded in (2,2^775,2^201,2^775^201):
        G=g.copy();w=(encoded&~1)<<1;r=encoded&1
        for j in path:
            if w>>j&1:w^=G[j];r^=1
            G=lc(G,j)
        if (w,r)==(286,1):print("seed affine mask",encoded,flush=True)

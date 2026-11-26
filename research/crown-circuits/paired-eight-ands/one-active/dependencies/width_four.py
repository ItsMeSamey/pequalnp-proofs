"""Verify the saturated five-helper libraries for one dirty switch of width four."""
from sys import argv
from functools import cache
from itertools import combinations
from operator import or_
from functools import reduce

@cache
def trees(mask):
    if mask.bit_count()==1:
        return {frozenset()}
    out=set()
    a=(mask-1)&mask
    while a:
        b=mask^a
        if a<b:
            for first in trees(a):
                for second in trees(b):
                    out.add(first|second|{mask})
        a=(a-1)&mask
    return out

axes=int(argv[1]) if len(argv)>1 else 7
T=sum(1<<(2*i) for i in range(1,5))
K=3|(1<<10)|(1<<12)
choices=[sum(1<<(2*j+(s>>j&1)) for j in range(axes)) for s in range(1<<axes)]
@cache
def zero(mask):
    event=0
    for i,selected in enumerate(choices):
        m=mask|T if mask&selected&3 else mask
        if not(m&selected&~3): event|=1<<i
    return event

def pack(events,need,used=0):
    if not need:return True
    if len(events)<need or sum(e.bit_count() for e in events[:need])+used.bit_count()>1<<axes:return False
    for i,e in enumerate(events):
        if not(e&used) and pack(events[i+1:],need-1,used|e):return True
    return False

total=survive=0
for a in trees(T):
    for b in trees(K):
        bank={1<<j for j in range(2*axes)}|a|(b-{K})
        masks=bank|{x|y for x,y in combinations(bank,2)}
        events=sorted({zero(m) for m in masks if zero(m) and not(zero(m)&zero(K))},key=int.bit_count)
        small=[]
        for e in events:
            if not any(x&e==x for x in small):small.append(e)
        total+=1
        survive+=pack(small,11,zero(K))
print(len(trees(T)),len(trees(K)),total,survive)

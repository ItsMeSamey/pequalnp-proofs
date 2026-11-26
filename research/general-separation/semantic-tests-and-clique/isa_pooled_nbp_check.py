"""Verify accepting-path multiplicities for pooled two-half address queries."""
from itertools import product

def paths(index,words,payload,group,lo,retest=True):
    if index not in group:
        return 0
    lower=(1<<lo)-1
    prefix=words[index]>>lo
    return sum(1 for j,bit in enumerate(payload) if bit and j>>lo==prefix
               for guessed in group if words[guessed]&lower==j&lower
               and (not retest or guessed==index))

count=0
false_without=False
for words in product(range(4),repeat=3):
    for payload in product(range(2),repeat=4):
        for i in range(3):
            value=sum(paths(i,words,payload,g,1) for g in ((0,1),(2,)))
            assert value==payload[words[i]]
            false_without |= (not value and paths(i,words,payload,(0,1),1,False)>0)
            count+=1
assert false_without
print(count,'assignments; omission of final index retest gives false positives')

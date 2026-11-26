"""Verify the rejection rectangle on every possible raw pin mask of class 1961."""
from itertools import product
T=(4096,1024,256)

def decorated(child,terminal,state):
    if state==0:return 1<<(2*terminal+1)
    return (1<<(2*terminal))|(1<<(2*child+state-1))

factors=[[decorated(j,6-j,s) for s in range(3)] for j in range(3)]+[[1<<6,1<<7]]
signatures=set()
for selector in range(128):
    seen=0
    for j in reversed(range(7)):
        if j>=3 or T[j]&seen:seen|=1<<(2*j+((selector>>j)&1))
    signatures.add(seen)
words=[a|b|c|d for a,b,c,d in product(*factors)]
assert len(set(words))==54 and set(words)==signatures
for raw in range(1<<14):
    projected=[[s for s in f if not raw&s] for f in factors]
    observed={a|b|c|d for a,b,c,d in product(*projected)}
    assert observed=={s for s in signatures if not raw&s}
print('1961:',len(signatures),'signatures;',1<<14,'verified Cartesian rejection rectangles')

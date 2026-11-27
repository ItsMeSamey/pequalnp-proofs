"""Pure finite checks for forks after omitting at most four maximal negatives."""
from itertools import combinations
from collections import Counter
from pathlib import Path
import runpy
rows=runpy.run_path(str(Path(__file__).parent/'fano20-canonical'/'encode.py'))['cases']()
flags={m for m,p in rows if p}; neg=[m for m,p in rows if not p]
def pair(a,b): return (1<<a)|(1<<b)
def edge(a,b): return pair(a,b) in flags
def has(n,a,b): return pair(a,b)&~n==0
assert all(sum(bool(n&(1<<a)) for n in neg)==6 for a in range(12))
swaps={}
for a,b in combinations(range(12),2):
    swaps[a,b]=sum(1<<i for i,n in enumerate(neg) if any(
        edge(a,c) and has(n,b,c) or edge(b,c) and has(n,a,c)
        for c in range(12) if c not in (a,b)))
assert Counter(w.bit_count() for (a,b),w in swaps.items() if a//6==b//6)=={8:16,10:14}
protect=[]
for p in range(6):
    for l in range(6,12):
        if edge(p,l):
            protect.append(sum(any(edge(v,l) and edge(p,w) and has(n,v,w)
                               for v in range(6) if v!=p
                               for w in range(6,12) if w!=l) for n in neg))
assert Counter(protect)=={5:8,9:8}
ind=[c for c in range(4096) if not any(c&f==f for f in flags)]
assert {c for c in ind if c.bit_count()>=6}=={63,63<<6}
hist=Counter(); exceptions=[]
for j in range(5):
    for omit in combinations(range(21),j):
        o=sum(1<<i for i in omit)
        ambiguous=[(a,b) for (a,b),w in swaps.items() if not w&~o]
        hist[j,len(ambiguous)]+=1
        if len(ambiguous)>=2:
            assert len(ambiguous)==2
            merged=pair(*ambiguous[0])|pair(*ambiguous[1])
            assert merged.bit_count()==4
            assert max(c.bit_count() for c in ind if not c&merged)==4
            exceptions.append((omit,ambiguous))
assert len(exceptions)==2
valid=[{c for c in range(4096) if all((c&~n)&f for f in flags)} for n in neg]
paircost=Counter(min(c.bit_count() for c in valid[i]&valid[j])-1
                 for i,j in combinations(range(21),2))
assert paircost=={8:36,9:58,10:76,11:40}
print(hist,exceptions,paircost,sep='\n')

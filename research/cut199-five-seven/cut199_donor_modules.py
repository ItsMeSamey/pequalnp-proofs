"""Test all left raw-variable donor subsets against frozen right cofactor modules."""
import json
from itertools import combinations
from pathlib import Path
root=Path(__file__).resolve().parent
graph=json.loads((root/'cut199-two-raw-fork6-22.json').read_text())
L=[0,1,2,6,7];R=[3,4,5,8,9,10]
def expand(x,s):return sum((x>>j&1)<<v for j,v in enumerate(s))
F=[[any(((expand(x,L)|expand(y,R))>>a)&((expand(x,L)|expand(y,R))>>b)&1 for a,b in graph['edges']) for y in range(64)] for x in range(32)]
def check(s):
    inside=[i for i in range(5) if s>>i&1];outside=[i for i in range(5) if not(s>>i&1)]
    size=1<<len(inside);full=(1<<size)-1;profile=set();bad=None;forced={}
    for y in range(64):
        nonconstant={}
        for a in range(1<<len(outside)):
            word=sum(F[expand(i,inside)|expand(a,outside)][y]<<i for i in range(size))
            if word not in (0,full):nonconstant[word]=expand(a,outside)
        if len(nonconstant)>1:
            bad=[y,list(nonconstant.items())[:2]];break
        profile.update(nonconstant)
        if nonconstant:forced[y]=next(iter(nonconstant))
    if not bad:
        for y,a in forced.items():
            for z,b in forced.items():
                if not y&~z and a&~b:
                    bad=dict(smaller=y,larger=z,smaller_word=a,larger_word=b);break
            if bad:break
    M=len(profile);K=(M-1).bit_length()
    comparisons=sum(not(u&~v) for u in profile for v in profile)
    if M==1<<K and comparisons<3**K:K+=1
    return dict(mask=s,left=[L[i] for i in inside],bad=bad,profiles=M,ordered=comparisons,right_bits=None if bad else K)
if __name__=='__main__':
    records=[check(s) for s in range(1,32)]
    print([v['left'] for v in records if v['bad']])
    print([(v['left'],v['right_bits']) for v in records if not v['bad']])
    (root/'cut199-raw-left-donor-modules.json').write_text(json.dumps(records))

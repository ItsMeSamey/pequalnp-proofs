"""Enumeration of the target and four-subcube of bad competitors."""
from itertools import combinations
from functools import reduce
names=['a','b','i','j','p','q','v']
core=[('a','i'),('i','j'),('j','b'),('i','p'),('j','q')]
def matrix(labels,edges):
    A=[0]*len(labels)
    for u,v in edges:
        i=labels.index(u);j=labels.index(v);A[i]|=1<<j;A[j]|=1<<i
    return A
def valid(A,x):return all(not(x>>i&1) or (x&r).bit_count()%2==0 for i,r in enumerate(A))
def score(x,weights):return reduce(int.__xor__,(w for i,w in enumerate(weights) if x>>i&1),0)
A=matrix(names,core+[('v',i) for i in 'ijpq'])
weights=[1,2,4,0,0,0,4]
assert [x for x in range(128) if valid(A,x) and score(x,weights)==7]==[67]
lift=names[:6]+['l','r','k','m']
shore={'a','j','p'}
edges=core+[('r' if v in shore else 'l',v) for v in 'ijpq']+[('l','k'),('k','m'),('m','r')]
B=matrix(lift,edges)
def genuine(x):return x>>6&3==3 and score(x,weights[:6])==3
good=[x for x in range(1<<len(B)) if valid(B,x) and genuine(x)]
assert good==[195]
X=good[0];cube=[s for s in range(1<<len(B)) if not(s&~X)]
assert len(cube)==16 and all(valid(B,s) for s in cube)
def dot(a,b):return (a&b).bit_count()%2
for rows in combinations(range(1,16),3):
    assert any(all(not dot(r,d) for r in rows) for d in range(1,16))
print('Unique native mask 67 and split mask 195. All 16 subsets feasible; no three affine rows isolate.')

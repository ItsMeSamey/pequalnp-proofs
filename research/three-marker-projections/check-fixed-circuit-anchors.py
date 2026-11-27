from itertools import combinations
from functools import reduce
from operator import xor

keys = [10, 8, 12, 1, 5, 2, 3, 15, 14]
tag = 232
basis = [61, 75, 143, 263]
anchors = [61, 118, 143, 314]
form = 23

def total(mask):
    return reduce(xor, (a for i,a in enumerate(keys) if (mask>>i)&1), 0)

def span(words):
    values = {0:0}
    for i,w in enumerate(words):
        values.update({v^w:q^(1<<i) for v,q in list(values.items())})
    return values

relations = [x for x in range(1,1<<len(keys)) if total(x)==0]
circuits = [x for x in relations if all(x==y or (x&y)!=y for y in relations)]
even = [x for x in circuits if (x&tag).bit_count()%2==0]
coords = span(basis)
assert set(span(anchors))==set(coords)==set(span(even)) and set(anchors)<=set(even)
def pairing(x,y):
    i,j=coords[x],coords[y]
    return sum(((form>>a)&1)*(((i>>s)&(j>>t)&1)^((i>>t)&(j>>s)&1)) for a,(s,t) in enumerate(combinations(range(4),2)))%2
assert all(any(pairing(x,y) for y in coords) for x in coords if x)
positives=[]
for g in range(16):
    mismatch=sum(((tag>>i ^ (g&k).bit_count())&1)<<i for i,k in enumerate(keys))
    active=[x for x in relations if not x&mismatch]
    for x,y in combinations(active,2):
        if pairing(x,y):
            assert x not in anchors and y not in anchors
            positives.append((g,x,y))
assert positives
print(len(relations),len(circuits),len(even),len(positives),positives[0])

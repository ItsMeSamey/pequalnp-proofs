from itertools import combinations
from random import Random

def feature(x,terms):
    return sum(1<<i for i,t in enumerate(terms) if x&t==t)
def rank(rows):
    piv={}
    for x in rows:
        while x and x.bit_length() in piv:x^=piv[x.bit_length()]
        if x:piv[x.bit_length()]=x
    return len(piv)

rng=Random(190)
for _ in range(300):
    n=rng.randrange(2,8);d=rng.randrange(1,4)
    edges=[(i,j) for i in range(n) for j in range(n) if i!=j and rng.randrange(10)==0]
    conflict=[(1<<i)|(1<<j) for i,j in combinations(range(n),2) if rng.randrange(8)==0]
    ext=[x for x in range(1<<n) if all(not(x>>i&1) or x>>j&1 for i,j in edges)
         and all(x&m!=m for m in conflict)]
    terms=[t for t in range(1<<n) if t.bit_count()<=d]
    closure=set()
    for x in terms:
        while True:
            y=x
            for i,j in edges:
                if x>>i&1:x|=1<<j
            if y==x:break
        if all(x&m!=m for m in conflict):closure.add(x)
    assert rank(feature(x,terms) for x in ext)==len(closure)
    assert rank(feature(x,terms) for x in closure)==len(closure)
# Standalone signed-star example q=4: pins A0,B0,C1 false; A1 true;
# the low bit is a separating functional, so its A-coset excludes A1.
q=4
pins={0:1,4:1,9:1,1:0}   # bit 1 means FALSE here
best=0
for false in range(1<<(3*q)):
    if not all(false>>i&1==v for i,v in pins.items()):continue
    if any(false>>a&false>>(q+b)&false>>(2*q+(a^b))&1
           for a in range(q) for b in range(q)):continue
    best=max(best,false.bit_count())
assert best==6 and 3*q-best-1==5
print('300 exact exterior ranks and pinned q=4 optimum degree 5 verified')

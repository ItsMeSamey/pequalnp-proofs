from first import dense,fast
from random import Random
from itertools import product
def edges(t,kind):
    pairs=set()
    def add(i,j):
        if i!=j: pairs.add(tuple(sorted((i,j))))
    for x,y in product(range(t),repeat=2):
        i=x*t+y
        if kind=="grid":
            if x+1<t: add(i,i+t)
            if y+1<t: add(i,i+1)
        else:
            for u,v in (((x+2*y)%t,y),((x+2*y+1)%t,y),(x,(y+2*x)%t),(x,(y+2*x+1)%t)):
                add(i,u*t+v)
    return sorted(pairs)
def encode(d,rows,basepins,dummies):
    pos=[]; neg=[]
    for r in rows:
        pos.append(sum(1<<(l-1) for l in r if l>0))
        neg.append(sum(1<<(-l-1) for l in r if l<0))
    pos.extend([1]*(d-len(rows))); neg.extend([1]*(d-len(rows)))
    a=b=(1<<d)-1
    for i,v in list(basepins)+[(i,0) for i in dummies]:
        if v: a &= ~(1<<i)
        else: b &= ~(1<<i)
    return d,pos,neg,a,b
def nextpow(n): return 1<<(n-1).bit_length()
def bomb(*_): raise AssertionError("expensive fallback unexpectedly called")
for kind in ("grid","mgg"):
    n=16
    es=edges(4,kind)
    rows=[(-u-1,-v-1) for u,v in es]
    d=nextpow(max(n,len(rows)))
    for pins,expected in (([],"SAT"),([(u,1) for u in es[0]],"UNSAT")):
        status,route,_=dense(*encode(d,rows,pins,range(n,d)),fallback=bomb)
        assert (status,route)==(expected,"SCC")
    print(kind,n,len(es),d,2*d*d+2*d,"bits: SCC SAT/UNSAT")
k=4
es=edges(2,"grid")
e=len(es); tags=k+2*e-1; copies=1<<k; C=6*e-3
d=nextpow(max(tags,C))*copies
rows=[]; pins=[]; expectedword=0
# Source address is (gate tag, original input word).
def address(tag,z): return tag*copies+z
for z in range(copies):
    wire=[(z>>i)&1 for i in range(k)]
    for i,v in enumerate(wire): pins.append((address(i,z),v))
    def literal(tag): return address(tag,z)+1
    def gate(i,j,nand):
        a,b=literal(i),literal(j); o=literal(len(wire))
        out=-o if nand else o
        rows.extend([(-a,-b,out),(a,-out),(b,-out)])
        wire.append((wire[i]&wire[j])^int(nand))
    for i,j in es: gate(i,j,True)
    acc=k
    for j in range(1,e):
        gate(acc,k+j,False)
        acc=len(wire)-1
    for i,v in enumerate(wire): expectedword |= v<<address(i,z)
data=encode(d,rows,pins,range(tags*copies,d))
assert dense(*data,fallback=bomb)==("SAT","UP",expectedword)
# z=0 is independent; forcing its computed output false must conflict.
bad=encode(d,rows,pins+[(address(tags-1,0),0)],range(tags*copies,d))
assert dense(*bad,fallback=bomb)==("UNSAT","UP",None)
print("batch",copies,"copies;",k,"inputs",tags-k,"gates per copy;",tags*copies,"active vars",len(rows),"clauses",len(pins),"input pins",d-tags*copies,"dummy pins",d,"D",2*d*d+2*d,"bits: exact unique witness, conflicting extra output")
assert fast(3,[(1,),(-1,2,3),(-2,-3)],fallback=bomb)[1]=="UP+SCC"
assert fast(3,[(1,2,3)],fallback=lambda n,r:("SKIP_FACTOR",None,0))[:2]==("SKIP","FALLBACK")
assert dense(1,[1],[1],0,0)[:2]==("UNSAT","DOMAIN")
rng=Random(997)
for _ in range(300):
    n=rng.randint(1,6)
    cs=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randint(0,min(n,3)))) for _ in range(rng.randrange(11))]
    status,_,word=fast(n,cs)
    if status=="SKIP": continue
    def check(w): return all(any(bool(w&(1<<(abs(l)-1)))==(l>0) for l in c) for c in cs)
    assert (status=="SAT")==any(check(w) for w in range(1<<n))
    if status=="SAT": assert check(word)

for invalid in (9,-1,True,1.0,"1",None):
    try:
        fast(3,[(1,2,3)],fallback=lambda *_:("SAT",invalid,0))
    except AssertionError as error:
        assert str(error)=="invalid original witness word"
    else:
        raise AssertionError("malformed sparse fallback word escaped")
assert fast(3,[(1,2,3)],fallback=lambda *_:("SAT",7,0))==("SAT","FALLBACK",7)
print("six malformed sparse fallback words rejected; valid boundary word accepted")

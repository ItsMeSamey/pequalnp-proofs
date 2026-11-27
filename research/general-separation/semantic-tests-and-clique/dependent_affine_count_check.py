"""Small exhaustive K=2 matroid partitions, affine slice corrections and controls."""
from itertools import combinations,product
from collections import Counter
from random import Random

def span(vs):
    s={0}
    for v in vs:s|={a^v for a in s}
    return s

def split(vs):
    for mask in range(1<<len(vs)):
        bins=[[i for i in range(len(vs)) if mask>>i&1==b] for b in (0,1)]
        if all(len(span(vs[i] for i in ids))==1<<len(ids) for ids in bins):return bins
    return None

def condition(ls):
    basis=[]
    while True:
        U=span(basis)
        colors=[]
        for row in ls:
            pairs=[(i,min(v^u for u in U)) for i,(v,c) in enumerate(row) if v not in U]
            vs=[v for i,v in pairs]
            bins=split(vs)
            bad=next((ids for l in range(1,len(vs)+1) for ids in combinations(range(len(vs)),l)
                      if l>2*(len(span(vs[i] for i in ids)).bit_length()-1)),None)
            assert (bins is None)==(bad is not None)
            if bad:
                old=len(basis)
                for i in bad:
                    v=row[pairs[i][0]][0]
                    if v not in span(basis):basis.append(v)
                assert 0<2*(len(basis)-old)<len(bad)
                break
            colors.append([[pairs[j][0] for j in ids] for ids in bins if ids])
        else:return basis,colors

def weights(ls,x):
    return [sum(((v&x).bit_count()%2)^c for v,c in row) for row in ls]

def check(ls,q,single=None,toggle=False):
    basis,colors=condition(ls)
    assert len(basis)*2<=sum(map(len,ls))
    U=span(basis)
    correction=Counter()
    total=0
    for z in product(range(2),repeat=len(basis)):
        xs=[x for x in range(1<<q) if tuple((v&x).bit_count()%2 for v in basis)==z]
        assert len(xs)==1<<(q-len(basis))
        decoded={x:[0]*len(ls) for x in xs}
        exceptions=[]
        for j,row in enumerate(ls):
            offset={sum(((v&x).bit_count()%2)^c for v,c in row if v in U) for x in xs}
            assert len(offset)==1
            for x in xs:decoded[x][j]=next(iter(offset))
            for ids in colors[j]:
                m=len(ids)
                pats={x:tuple(((row[i][0]&x).bit_count()%2)^row[i][1] for i in ids) for x in xs}
                assert set(Counter(pats.values()).values())=={len(xs)//(1<<m)}
                bad=set()
                for x,p in pats.items():
                    w=sum(p)
                    B=m//2-1
                    rep=w if m<2 else B+(w-B)%2
                    decoded[x][j]+=rep
                    if rep!=w:bad.add(x)
                exceptions.append(bad)
        def pred(x,w):
            if toggle:return int(((w[0]+2*w[1]+(x&1))%4)<2) ^ int(x==single)
            if single is not None:return int(x==single and w==weights(ls,single))
            return int(((w[0]+2*w[1]+(x&1))%4)<2)
        total+=sum(pred(x,decoded[x]) for x in xs)
        seen=set()
        for bad in exceptions:
            for x in bad-seen:
                d=pred(x,weights(ls,x))-pred(x,decoded[x])
                total+=d
                correction[d]+=1
            seen |= bad
    assert total==sum(pred(x,weights(ls,x)) for x in range(1<<q))
    return len(basis),correction
rng=Random(1920)
q=6
ls=[[(v,i%2) for i,v in enumerate(row)] for row in [[1,1,1,0,4,8],[2,2,2,0,16,32]]]
assert check(ls,q)[0]==2
acc=Counter()
for _ in range(24):
    rows=[[(rng.randrange(10),rng.randrange(2)) for i in range(q)] for j in range(2)]
    acc.update(check(rows,q)[1])
    singleton=rng.randrange(1<<q)
    check(rows,q,singleton)
    check(rows,q,singleton,True)
assert acc[1] and acc[-1]
# Adapt second list based only on the previous answer, enumerate even impossible histories.
scores=Counter()
for x in range(1<<q):
    a=weights(ls[:1],x)[0]
    b=weights([ls[a%2]],x)[0]
    scores[a,b]+=1
for a,b in product(range(q+1),repeat=2):
    assert scores[a,b]==sum(weights([ls[0],ls[a%2]],x)==[a,b] for x in range(1<<q))
k=(q+1).bit_length()-1
def read(x):
    return tuple(sum(((x>>(i+j))&1) for j in range(min(k,q-i)) for _ in range(1<<j)) for i in range(0,q,k))
assert len({read(x) for x in range(1<<q)})==1<<q
print('two conditioned dimensions, 72 seeded systems, correction signs',acc[1],acc[-1],'; adaptive and universal controls passed')

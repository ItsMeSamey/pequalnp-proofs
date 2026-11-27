"""Original signed-star guard with two genuine source witnesses and repeated clauses."""
from itertools import product
from random import Random

def differences(pos,h):
    a,b = ([sum(1<<(i^u) for i in positions) for u in range(h)] for positions in pos[:2])
    c = sum(1<<i for i in pos[2])
    return {(u,v) for u in range(h) for v in range(h) if a[u]&b[v]&c}

def check():
    h=64
    src=[(4,5,4),(-4,-5,-5)]
    units=[(-i,-i,-i) for i in (1,2,3)]
    expected={(u,v) for u in range(h) for v in range(h) if u or v}
    rng=Random(1649)
    for attempt in range(256):
        normals=[]
        for i in range(h-len(src)-len(units)):
            chosen=rng.randrange(3)
            normals.append(tuple(-j if j-1==chosen else j for j in (1,2,3)))
        cs=src+units+normals
        guard=[{i for i in range(5,h) if cs[i][j]>0} for j in range(3)]
        if differences(guard,h)!=expected:
            continue
        count=0
        for bits in product((0,1),repeat=5):
            def value(l):
                return bits[abs(l)-1] ^ (l<0)
            if all(any(map(value,c)) for c in cs):
                pos=[{i for i,c in enumerate(cs) if not value(c[j])} for j in range(3)]
                assert differences(pos,h)==expected
                count+=1
        assert count==2
        print(f'{count} physical models, all {h*h-1} nonzero differences, trial {attempt+1}')
        return
    raise AssertionError("fixed-seed guard search failed")

if __name__=='__main__':
    check()

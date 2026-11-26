"""Small exhaustive checks of terminal connectivity, path predicate and syndrome assembly."""
from functools import lru_cache
from itertools import combinations

def test_matchings():
    n=5
    edges=list(combinations(range(n),2))
    checks=0
    for G in range(1<<len(edges)):
        neighbors=[0]*n
        for i,(a,b) in enumerate(edges):
            if G>>i&1:
                neighbors[a]|=1<<b; neighbors[b]|=1<<a
        @lru_cache(None)
        def perfect(mask):
            if not mask:
                return True
            a=(mask & -mask).bit_length()-1
            rest=mask^(1<<a)
            return any(perfect(rest^(1<<b)) for b in range(n) if rest&neighbors[a]&(1<<b))
        for terminals in (0b11111,0b01111,0b00111):
            F={s for s in range(1<<n) if s&~terminals==0 and perfect(((1<<n)-1)^s)}
            if not F:
                continue
            first=next(iter(F)); found={first}; queue=[first]
            while queue:
                s=queue.pop()
                for p in F-found:
                    if (s^p).bit_count()<=2:
                        queue.append(p); found.add(p)
            assert F==found
            checks+=1
    return checks

def test_paths():
    for signs in range(256):
        good=False
        for y in range(1<<9):
            if not y&1 or y>>8&1:
                continue
            if all(not(y>>i&1) or ((y>>(i+1)&1)^(signs>>i&1)) for i in range(8)):
                good=True
                break
        assert good==bool(signs)
    return 256

def syndrome(bits):
    if len(bits)==1:
        return bits[0],0
    mid=len(bits)//2
    a,u=syndrome(bits[:mid]); b,v=syndrome(bits[mid:])
    return a^b,(u^v)|(b*mid)

def test_hamming():
    m=4; n=(1<<m)-1
    code=[]
    for x in range(1<<n):
        vals=[0]+[(x>>i)&1 for i in range(n)]
        expected=0
        for i,val in enumerate(vals):
            if val:
                expected^=i
        assert syndrome(vals)[1]==expected
        if not expected:
            code.append(x)
    assert len(code)==1<<(n-m)
    assert min(x.bit_count() for x in code if x)==3
    return len(code)
print(test_matchings(),"nonempty matching families,",test_paths(),"path-sign patterns,",test_hamming(),"Hamming words verified.")

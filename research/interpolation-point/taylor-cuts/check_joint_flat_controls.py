"""Tiny source-grounded safe-path and quadratic-relation controls."""
from itertools import combinations,product
from clause_rank_drop_hybrid import count

def bit(x,i):
    return bool(x>>(i-1)&1)

def holds(x,rows):
    return all(any(bit(x,abs(l))==(l>0) for l in c) for c in rows)

def safe(n,src):
    rows=[]
    groups=[]
    off=n+1
    for c in src:
        g=list(range(off,off+len(c)))
        groups.append(g)
        off+=len(g)
        rows.append(g)
        rows.extend((-a,-b) for a,b in combinations(g,2))
        rows.extend((-a,l) for a,l in zip(g,c))
    paths=[(x,js) for x in range(1<<n) for js in product(*(range(len(c)) for c in src))
           if all(bit(x,abs(c[j]))==(c[j]>0) for c,j in zip(src,js))]
    for flag in (False,True):
        val,w,stats=count(off-1,rows,group_equal=flag)
        assert val==len(paths)==sum(holds(x,rows) for x in range(1<<(off-1)))
        if w is not None:
            js=tuple(next(i for i,a in enumerate(g) if bit(w,a)) for g in groups)
            assert holds(w,rows) and (w&((1<<n)-1),js) in paths
        else:
            assert not paths
        print("safe",n,flag,"models",sum(holds(x,src) for x in range(1<<n)),"paths",val,stats)

def algebra():
    rows=[(-1,-i) for i in range(2,6)]
    for bits in product((0,1),repeat=4):
        if (bits[0]&bits[1])^(bits[2]&bits[3]):
            rows.append(tuple(-v if b else v for v,b in zip(range(6,10),bits)))
    def original(x):
        return not any(bit(x,1) and bit(x,i) for i in range(2,6)) and (
            (bit(x,6) and bit(x,7))==(bit(x,8) and bit(x,9)))
    assert all(holds(x,rows)==original(x) for x in range(512))
    for flag in (False,True):
        val,w,stats=count(9,rows,group_equal=flag)
        assert val==170==sum(map(original,range(512))) and original(w)
        print("algebra",flag,val,stats)

if __name__=="__main__":
    safe(1,[(1,1,1),(-1,-1,-1)])
    safe(2,[(1,2,1),(-1,2,-1)])
    algebra()

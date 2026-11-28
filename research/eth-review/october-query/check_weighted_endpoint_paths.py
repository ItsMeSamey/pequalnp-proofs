"""Physical characteristic-two endpoint coefficient versus signed raw model fingerprint."""
from itertools import product

def mul(a,b): return (a if b&1 else 0)^([0,2,3,1][a] if b&2 else 0)
def plus(p,q): return [a^b for a,b in zip(p,q)]
def times(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q): r[i+j]^=mul(a,b)
    return r
def shift(p):
    out=[0]*len(p)
    for j,a in enumerate(p):
        for i in range(j+1):
            if i&~j==0: out[i]^=a
    return out

def tables(cs,ds,swap):
    roots=max(abs(l) for c in cs for l in c)
    copy=roots
    edges=[]
    occ=[]
    for c,path in zip(cs,ds,strict=True):
        for l,d in zip(c,path,strict=True):
            prev=abs(l)-1
            for _ in range(d-1):
                edges.append((prev,copy))
                prev=copy
                copy+=1
            edges.append((prev,-len(occ)-1))
            occ.append((l,d))
    e=len(edges)
    polys=[[0]*(2*e+1) for _ in range(1<<roots)]
    pair={}
    for a,b in product((0,1),repeat=2):
        small=[0,0,0]
        for x in (0,1):
            small=plus(small,times([1^a,x],[1^b,x]))
        pair[a,b]=small
    for cw in range(1<<copy):
        for yw in range(1<<len(occ)):
            pos=0
            for clause in cs:
                ok=False
                for _ in clause:
                    literal,d=occ[pos]
                    ok|=(yw>>pos&1)==((literal>0)^1^(d&1))
                    pos+=1
                if not ok: break
            else:
                p=[1]
                for left,right in edges:
                    a=cw>>left&1
                    b=((cw>>right&1) if right>=0 else (yw>>(-right-1)&1))^swap
                    p=times(p,pair[a,b])
                k=cw&((1<<roots)-1)
                polys[k]=plus(polys[k],p)
    assert all(not any(p[:e]) for p in polys)
    return [p[e:] for p in polys]

def weighted(tables,rs):
    out=[0]*len(tables[0])
    for bits,p in enumerate(tables):
        w=1
        for j,r in enumerate(rs):
            if not (bits>>j&1): w=mul(w,r)
        out=plus(out,[mul(w,x) for x in p])
    return out

def direct(cs,rs):
    out=count=0
    for w in range(1<<len(rs)):
        if not all(any((w>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs): continue
        count+=1
        val=1
        for j,r in enumerate(rs):
            if w>>j&1: val=mul(val,r)
        out^=val
    return count,out

if __name__=='__main__':
    cs=((1,2),(1,-2))
    for paths in (((1,1),(1,1)),((2,1),(3,1))):
        p=tables(cs,paths,0)
        switched=tables(cs,paths,1)
        for rs in product(range(4),repeat=2):
            value=weighted(p,rs)
            count,want=direct(cs,rs)
            assert count==2 and value[0]==want
            assert shift(value)==weighted(switched,rs)
        assert direct(cs,(2,2))==(2,1)
    print('PASS 32 GF4 coefficient and full normalized swap tests; 2-model signed CNF, path lengths 1/2/3, fingerprint (omega,omega)=1')

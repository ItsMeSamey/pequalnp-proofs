"""Balanced-tree DP with boundary-only coordinate enumeration and original mask payloads."""
from itertools import product
def bit_indices(bits):
    while bits:
        low = bits & -bits
        yield low.bit_length() - 1
        bits ^= low

def basis(vectors):
    rows={}
    for x in vectors:
        for i in sorted(rows,reverse=True):
            if x>>i&1: x ^= rows[i]
        if not x: continue
        i=x.bit_length()-1
        for j,old in list(rows.items()):
            if old>>i&1: rows[j]=old^x
        rows[i]=x
    return tuple(rows[i] for i in sorted(rows))

def intersection(left,right):
    pivots={}
    common=[]
    for x,y in [(v,0) for v in right]+[(v,v) for v in left]:
        while x:
            i=x.bit_length()-1
            if i not in pivots:
                pivots[i]=(x,y)
                break
            row,trace=pivots[i]
            x ^= row
            y ^= trace
        if not x and y: common.append(y)
    return basis(common)

def coordinates(x,rows):
    mask=0
    for j in reversed(range(len(rows))):
        if x>>(rows[j].bit_length()-1)&1:
            x ^= rows[j]
            mask ^= 1<<j
    return None if x else mask

def wedge(u,v):
    out=0
    for a,b in ((u,v),(v,u)):
        for j in bit_indices(a):
            out ^= (b&((1<<j)-1)) << (j*(j-1)//2)
    return out

def insert(rows,x,record):
    while x:
        p=x.bit_length()-1
        if p not in rows:
            rows[p]=(x,record)
            return
        x ^= rows[p][0]
def run(rows):
    count=[0,0,0]
    n=len(rows)
    def make(ids):
        if len(ids)==1: return ids,None,None,basis([rows[ids[0]][0]])
        m=len(ids)//2
        a=make(ids[:m]);b=make(ids[m:])
        return ids,a,b,basis(a[3]+b[3])
    def words(bs):
        vals=[0]
        for b in bs: vals.extend([v^b for v in vals])
        return vals
    def ev(chart,z):
        a,b=chart;return ((z&a).bit_count()%2)|(((z&b).bit_count()%2)<<1)
    def walk(t,outer):
        ids,left,right,inside=t
        cols=intersection(inside,outer); vals=words(cols)
        charts=list(product(range(1<<len(cols)),repeat=2))
        count[0]+=1;count[1]=max(count[1],len(cols))
        out={}
        def add(key,u,v):
            fv=1|(u<<1)|(v<<(1+n))|(wedge(u,v)<<(1+2*n))
            insert(out.setdefault(key,{}),fv,(u,v))
        if left is None:
            i=ids[0];k,b,_=rows[i]
            for chart in charts:
                loc=coordinates(k,cols)
                ok=(loc is None or ev(chart,loc)==b)
                for uv in range(4 if ok else 1):
                    p=k if uv&1 else 0;q=k if uv&2 else 0
                    if p in vals and q in vals:add((chart,p,q),(1<<i) if uv&1 else 0,(1<<i) if uv&2 else 0)
        else:
            l,lv=walk(left,basis(outer+right[3]))
            r,rv=walk(right,basis(outer+left[3]))
            inter=sorted(set(lv)&set(rv))
            pairs=[next((i,rv.index(v^x)) for i,x in enumerate(lv) if v^x in rv) for v in cols]
            for (lc,p,q),lb in l.items():
                for (rc,s,t),rb in r.items():
                    if (p^s) not in vals or (q^t) not in vals:continue
                    if any(ev(lc,lv.index(x))!=ev(rc,rv.index(x)) for x in inter):continue
                    ds=[ev(lc,i)^ev(rc,j) for i,j in pairs]
                    ch=tuple(sum(((z>>k)&1)<<i for i,z in enumerate(ds)) for k in range(2))
                    for _,(u,v) in lb.values():
                        for _,(y,z) in rb.values():add((ch,p^s,q^t),u^y,v^z)
        count[2]=max(count[2],len(out))
        return out,vals
    tab,_=walk(make(tuple(range(n))),())
    def ht(u):
        h=0
        for i in range(n):
            if u>>i&1:h^=rows[i][2]
        return h
    for _,(u,v) in tab[((0,0),0,0)].values():
        h,g=ht(u),ht(v)
        if h and g and h!=g: return (u,v),count
    return None,count

for shift in (0,80,256):
    for conflict in (True,False):
        a,b=1<<shift,1<<(shift+1)
        base=[(a,0,0),(a,0,1),(a if conflict else b,1,0),(a if conflict else b,1,2)]
        rows=base+[(1<<(shift+2+j),j%4,j%4) for j in range(32)]
        witness,c=run(rows)
        assert c[0]==2*len(rows)-1 and c[1]<=1 and c[2]<=16
        assert (witness is None)==conflict
        if witness:
            u,v=witness;assert u|v==15
        print(shift,conflict,witness,c)

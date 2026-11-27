"""Simultaneous wedge span using the specified site order as a path decomposition."""
from frontier import basis,intersection
from recognizer import bit_indices

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

def transfers(before,after,k):
    source=basis(before+(k,))
    old_c=[coordinates(v,source) for v in before]
    new_c=[coordinates(v,source) for v in after]
    site_c=coordinates(k,source)
    def ev(x,y,c):
        return (x&c).bit_count()%2 | (((y&c).bit_count()%2)<<1)
    result={}
    for x in range(1<<len(source)):
        for y in range(1<<len(source)):
            old=sum(ev(x,y,c)<<(2*j) for j,c in enumerate(old_c))
            new=sum(ev(x,y,c)<<(2*j) for j,c in enumerate(new_c))
            result.setdefault(old,set()).add((new,ev(x,y,site_c)))
    return result

def solve(columns):
    cols=tuple(columns)
    if any(k<0 or not 0<=b<4 for k,b in cols): raise ValueError("invalid key/tag")
    n=len(cols)
    keys=[k for k,b in cols]
    prior=()
    states={(0,0,0):{0:(1,(0,0,0))}}
    max_width=0
    for i,(k,b) in enumerate(cols):
        after=intersection(basis(keys[:i+1]),basis(keys[i+1:]))
        max_width=max(max_width,len(after))
        trans=transfers(prior,after,k)
        new={}
        for (gamma,p,q),rows in states.items():
            for dest,tag in trans[gamma]:
                for choice in range(4 if tag==b else 1):
                    p1=p^(k if choice&1 else 0)
                    q1=q^(k if choice&2 else 0)
                    if coordinates(p1,after) is None or coordinates(q1,after) is None: continue
                    active=new.setdefault((dest,p1,q1),{})
                    for _,(u,v,z) in rows.values():
                        u1=u|((1<<i) if choice&1 else 0)
                        v1=v|((1<<i) if choice&2 else 0)
                        cross=(v if choice&1 else 0)^(u if choice&2 else 0)
                        z1=z^(cross<<(i*(i-1)//2))
                        feature=1|(u1<<1)|(v1<<(n+1))|(z1<<(2*n+1))
                        insert(active,feature,(u1,v1,z1))
        prior,states=after,new
    out={}
    for _,(u,v,z) in states[(0,0,0)].values(): insert(out,z,(u,v,z))
    return [record for _,record in out.values()],max_width

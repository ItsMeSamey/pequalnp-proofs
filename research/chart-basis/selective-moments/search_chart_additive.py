from itertools import combinations
from random import Random

def reduce_vec(x,p):
    for i,v in sorted(p.items(),reverse=True):
        if x>>i&1: x^=v
    return x

def insert(x,p):
    x=reduce_vec(x,p)
    if x:p[x.bit_length()-1]=x
    return x

def witness(cols,r,s,t):
    n=len(cols); safe={}; rows=[]
    for b in combinations(range(n),r):
        if s not in b or t in b:continue
        co={0:0}
        for i in b:co.update({v^cols[i]:w|1<<i for v,w in co.items()})
        if len(co)!=1<<r or co[cols[t]]>>s&1:continue
        c={j:1<<j|co[v] for j,v in enumerate(cols) if j not in b}
        d={i:1<<i|sum(1<<j for j in c if c[j]>>i&1) for i in b}
        for j in c:
            if j!=t and not (c[j]>>s&1):insert(c[j],safe)
        for i in b:
            if i!=s and not (c[t]>>i&1):insert(d[i]<<n,safe)
        rows.append((sum(1<<i for i in b),c[t]|d[s]<<n))
    p={}
    for b,v in rows:
        rem=insert((((1<<n)|b)<<(2*n))|v,p)
        if rem and rem.bit_length()<=2*n and reduce_vec(rem,safe):
            w=reduce_vec(rem,safe); h=w.bit_length()-1; z=1<<h
            for i,row in sorted(safe.items()):
                if (z&row).bit_count()%2:z^=1<<i
            return z,rows
if __name__=='__main__':
    rng=Random(459)
    for n in range(6,15):
        for _ in range(1500):
            r=rng.randrange(3,min(7,n-2)+1)
            cols=rng.sample(range(1,1<<r),n) if n<1<<r else [rng.randrange(1,1<<r) for i in range(n)]
            hit=witness(cols,r,0,1)
            if hit:
                print(cols,r,hit,flush=True);quit()
        print(n,flush=True)

from random import Random
from functools import reduce
from operator import xor

def rank(a):
    basis={}
    for v in a:
        while v and v.bit_length() in basis:
            v ^= basis[v.bit_length()]
        if v: basis[v.bit_length()]=v
    return len(basis)

def connected(a):
    if len(a)<2: return True
    basis={}
    peers=[{i} for i in range(len(a))]
    for i,v in enumerate(a):
        mask=1<<i
        while v and v.bit_length() in basis:
            w,b=basis[v.bit_length()]
            v ^= w
            mask ^= b
        if v:
            basis[v.bit_length()]=(v,mask)
        else:
            ids=[j for j in range(len(a)) if mask>>j&1]
            for j in ids: peers[j].update(ids)
    seen={0}
    while True:
        ext=set.union(*(peers[i] for i in seen))
        if ext==seen: return len(seen)==len(a)
        seen=ext

def flux(a,r):
    values=set()
    for d in range(1,1<<r,16):
        span={0}
        for e in a:
            if (d&e).bit_count()%2==0:
                span |= {x^e for x in span}
        values.update(x for x in span if x<16)
    return values

if __name__=='__main__':
    rng=Random(74393)
    for r in (6,7,8):
        for n in range(r+1,r+8):
            for _ in range(12000):
                E=rng.sample(range(16,1<<r),n)
                if rank(E)!=r or not connected(E) or not connected([e>>4 for e in E]): continue
                S=flux(E,r)
                if len(S)==7:
                    print(r,n,E,sorted(set(range(0,16,2))-S),flush=True)
                    quit()

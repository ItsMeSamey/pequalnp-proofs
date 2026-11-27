"""Test reversible selector banks on the entire state space, including mixed banks."""
from random import Random

def matrices(w,gates):
    k=len(gates)
    L=w+1
    identity=[1<<i for i in range(k*L)]
    sel=0
    staged=[identity.copy(),identity.copy()]
    for i,gate in enumerate(gates):
        off=i*L
        tag,*args=gate
        if tag=='T':
            a,b,c=args
            assert len(set(args))==3
            sel|=1<<(off+a)
            staged[1][off+c]^=1<<(off+b)
        else:
            a,c=(w,args[0]) if tag=='N' else args
            assert a!=c
            for rows in staged:
                rows[off+c]^=1<<(off+a)
    M=[a[-L:]+a[:-L] for a in staged]
    inv=[[((row>>((k-1)*L))|(row<<L))&((1<<(k*L))-1) for row in a] for a in staged]
    # Input to either inverse is first shifted backward, so pre-shift control bits
    # become selector bits at their shifted positions.
    sel_out=((sel>>((k-1)*L))|(sel<<L))&((1<<(k*L))-1)
    return M,inv,sel,sel_out

def lin(a,x):
    return sum(((r&x).bit_count()%2)<<i for i,r in enumerate(a))

def trial(w,gates,exhaustive=True):
    M,inv,s,t=matrices(w,gates)
    n=len(M[0])
    for j in (0,1):
        assert all(lin(inv[j],lin(M[j],1<<i))==1<<i and
                   lin(M[j],lin(inv[j],1<<i))==1<<i for i in range(n))
        assert all(((t&lin(M[j],1<<i)).bit_count()^(s&(1<<i)).bit_count())%2==0
                   for i in range(n))
    points=range(1<<n) if exhaustive else [rng.getrandbits(n) for _ in range(600)]
    images=set()
    for x in points:
        b=(s&x).bit_count()%2
        y=lin(M[b],x)
        assert lin(inv[(t&y).bit_count()%2],y)==x
        images.add(y)
    if exhaustive:
        assert len(images)==1<<n
    return len(points)

rng=Random(26113)
print(trial(3,[('T',0,1,2),('T',1,2,0)]))
print(trial(3,[('T',0,1,2),('N',0),('C',2,1)]))
print(trial(4,[('T',1,0,3),('N',1),('C',3,2),('T',3,1,0),('T',0,2,3)],False))

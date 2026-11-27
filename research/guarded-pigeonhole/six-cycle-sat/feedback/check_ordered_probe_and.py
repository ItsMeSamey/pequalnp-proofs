"""Whole-socket replay of the ordered probe cap."""
from itertools import permutations, combinations


def cycle(p, seq):
    for a,b in zip(seq,seq[1:]+seq[:1]):
        p[a]=b


def visit(p, a, b):
    x=p[a]
    while x!=a and x!=b:
        x=p[x]
    return x==b


def cap(n):
    if n==1:
        return [0,1,2],(0,2)
    if n==2:
        return [0,3,1,2],(1,3)
    return [n-1,n+1,1,0]+list(range(2,n-1))+[n],(1,n+1)


def physical(n,mask):
    N=3*n+2
    off=list(range(N))
    us=list(range(2,N,3))
    cycle(off,[0]+[i for u in us for i in (u,u+1)])
    cycle(off,[1]+[u+2 for u in us])
    switch=list(range(N))
    for j,u in enumerate(us):
        if mask>>j&1:
            cycle(switch,[u,u+1,u+2])
    p=[off[x] for x in switch]
    cuts=[0,1]+[u+1 for u in us]
    proj=[]
    for x in cuts:
        y=p[x]
        while y not in cuts:
            y=p[y]
        proj.append(cuts.index(y))
    expect=list(range(n+2))
    for color in (0,1):
        cycle(expect,[color]+[j+2 for j in range(n) if mask>>j&1==color])
    assert proj==expect
    f,(a,b)=cap(n)
    extension=list(range(N))
    for i,x in enumerate(cuts):
        extension[x]=cuts[f[i]]
    closed=[extension[x] for x in p]
    assert visit(closed,cuts[a],cuts[b])==(mask==0)
    return proj


if __name__=='__main__':
    for n in range(1,13):
        projections=[physical(n,m) for m in range(1<<n)]
        if n==4:
            isolated=set()
            for f in permutations(range(6)):
                fs=[[f[x] for x in p] for p in projections]
                for a,b in combinations(range(6),2):
                    accepted=[m for m,z in enumerate(fs) if visit(z,a,b)]
                    if len(accepted)==1:
                        isolated.add(accepted[0])
            assert set(range(16))-isolated=={6,9}
    print("8190 native settings passed; four-probe nonisolatable patterns: 6, 9")

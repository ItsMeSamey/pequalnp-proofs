"""Complete native socket permutations, with a private third socket per tap."""
from itertools import product
from check_sparse_signed_rings import orbit

def local(bit):
    return (0,2,1,3) if bit==0 else (0,3,2,1)
from check_ordered_probe_and import cycle

def model(lits,cs,modes,erase,taps):
    n=len(lits); nv=len(modes); nc=len(set(cs)); base=4*nv; cl=base+5*n
    p=list(range(cl+nc))
    for i,m in enumerate(modes):
        for j,k in enumerate(local(m)):p[4*i+j]=4*i+k
    for i in range(nv):
        for s in (0,1):
            target=4*i+2+s; start=p.index(target)
            for j,literal in enumerate(lits):
                if literal==(i,s):
                    u=base+5*j;p[start]=u;p[u]=u+1;start=u+1
            p[start]=target
    stitch=list(range(len(p)));cycle(stitch,[4*i+1 for i in range(nv)])
    p=[stitch[x] for x in p]
    for c in range(nc):cycle(p,[cl+c]+[base+5*j+3 for j,d in enumerate(cs) if c==d])
    e=list(range(len(p)));t=e.copy()
    for j in range(n):
        u=base+5*j
        if erase>>j&1:cycle(e,[u,u+1,u+2])
        if taps>>j&1:cycle(t,[u+1,u+3,u+4])
    z=[p[e[t[x]]] for x in range(len(p))]
    return (cl+1 if nc==2 else 1) in orbit(z,cl)

def audit(lits,cs):
    n=len(lits);nv=max(i for i,s in lits)+1;checked=0;errors=[]
    for modes in product(range(2),repeat=nv):
        for erase in range(1<<n):
            goods=[modes[i]==s and not (erase>>j&1) for j,(i,s) in enumerate(lits)]
            want=all(any(g for g,d in zip(goods,cs) if d==c) for c in set(cs))
            actual=False
            for taps in range(1<<n):
                got=model(lits,cs,modes,erase,taps)
                if got and not want and not errors:errors.append((modes,erase,taps))
                actual|=got;checked+=1
            assert not want or actual
    return checked,errors

if __name__=='__main__':
    cases=[
        ([(0,0),(0,1)],[0,1],False),
        ([(0,0),(0,1),(1,1),(1,0)],[0,1,0,1],False),
        ([(0,0),(1,0),(0,0),(1,1)],[0,1,0,0],False),
        ([(0,0),(0,0)],[0,1],True),
    ]
    for lits,cs,bypass in cases:
        count,errors=audit(lits,cs)
        assert bool(errors)==bypass
        print(count,errors)

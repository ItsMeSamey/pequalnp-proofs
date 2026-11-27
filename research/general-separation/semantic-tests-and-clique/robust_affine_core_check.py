"""Small exact controls for robust surjectivity under all private affine shifts."""
from itertools import combinations, combinations_with_replacement
from random import Random
from conditional_quadratic_image import closure,polar,basis
from hidden_cubing_polar import nullspace,apply


def environment(n):
    allbits=(1<<(1<<n))-1
    inputs=[sum(((x>>i)&1)<<x for x in range(1<<n)) for i in range(n)]
    linears=[0]
    for u in inputs:linears += [a^u for a in linears]
    return allbits,inputs,linears


def tables(forms,n,env):
    full,inputs,_=env
    out=[]
    for f in forms:
        tab=0
        for m in f:
            h=full
            for i,u in enumerate(inputs):
                if m>>i&1:h&=u
            tab^=h
        out.append(tab)
    return out


def robust(tabs,env):
    full,_,linears=env
    if not tabs:return True
    if len(tabs)==1:return all((tabs[0]^u) not in (0,full) for u in linears)
    a,b=tabs
    for l in linears:
        h=a^l
        for k in linears:
            j=b^k
            if not ((h&j) and (h&(full^j)) and ((full^h)&j) and ((full^h)&(full^j))):return False
    return True


def projected(forms,n,env):
    D,_,_=closure(forms,n)
    tabs=tables(forms,n,env)
    low=[]
    for d in D:
        p=0
        for j,t in enumerate(tabs):
            if d>>j&1:p^=t
        low.append(p)
    matrices=[polar(f,n) for f in forms]
    rows=[m>>(j*n)&((1<<n)-1) for d in D for m in [apply(matrices,d)] for j in range(n)]
    vectors=nullspace(rows,n)
    complement=[]
    for i in range(n):
        x=1<<i
        if len(basis(vectors+[x]))>len(vectors):
            vectors.append(x)
            complement.append(x)
    k=len(complement)
    compact=[sum(((t>>apply(complement,u))&1)<<u for u in range(1<<k)) for t in low]
    return robust(compact,environment(k))


def run():
    n=4;env=environment(n)
    monos=[(1<<a)|(1<<b) for a,b in combinations(range(n),2)]
    forms=[{t for j,t in enumerate(monos) if mask>>j&1} for mask in range(64)]
    yes=total=0
    for a,b in combinations_with_replacement(forms,2):
        pair=[a,b]
        actual=robust(tables(pair,4,env),env)
        assert actual==projected(pair,n,env)
        yes+=actual;total+=1
    print('unordered polar pairs',total,'robust',yes)
    assert (total,yes)==(2080,1008)
    rng=Random(441)
    for n in range(2,8):
        env=environment(n)
        for i in range(16):
            fs=[{(1<<a)|(1<<b) for a,b in combinations(range(n),2) if rng.randrange(2)} for j in range(1+i%2)]
            assert projected(fs,n,env)==robust(tables(fs,n,env),env)
    print('96 random systems through seven private bits passed')


if __name__=='__main__':run()

"""Independent recognition using a port cycle basis, validated by exhaustive inputs."""
from itertools import combinations
from random import Random

def nullspace(rows, n):
    basis = {}
    for v in rows:
        for i in sorted(basis,reverse=True):
            if v>>i & 1:
                v ^= basis[i]
        if v:
            basis[v.bit_length()-1]=v
    vectors=[]
    for j in range(n):
        if j not in basis:
            w=1<<j
            for i in sorted(basis):
                if (basis[i]&w).bit_count()%2:
                    w |= 1<<i
            vectors.append(w)
    return vectors

def port_cycles(clutter, n):
    cols=[(1<<len(clutter))-1]
    cols += [sum(1<<j for j,t in enumerate(clutter) if t>>i&1) for i in range(n)]
    piv,cycles={},[]
    for i,v in enumerate(cols):
        mask=1<<i
        while v and v.bit_length() in piv:
            z,mm=piv[v.bit_length()]
            v ^= z
            mask ^= mm
        if v:
            piv[v.bit_length()] = v,mask
        else:
            cycles.append(mask)
    comp=1
    while True:
        prev=comp
        for u in cycles:
            if comp&u: comp |= u
        if prev==comp: break
    return [u for u in cycles if comp&u]

def fiber(terms, killed, n):
    # terms are masks on remaining unate variables; killed are rows on selectors.
    kermask = 0
    for r in killed: kermask |= r
    good=set(t for j,t in enumerate(terms) if not(kermask>>j&1))
    if 0 in good: return True
    selectors=nullspace(killed,len(terms))
    odd=next((v for v in selectors if v.bit_count()%2),None)
    if odd is None: return not good
    if not good: return False
    C=[a for a in good if not any(b!=a and b&a==b for b in good)]
    for a,b,c in combinations(C,3):
        u=a^b^c
        if not any(u&t==t for t in C): return False
    cycles=port_cycles(C,n)
    for s in selectors:
        v=0
        for j,t in enumerate(terms):
            if s>>j&1: v ^= t
        marked=(v<<1)|(s.bit_count()%2)
        if any((marked&u).bit_count()%2 for u in cycles): return False
    return True

def brute(terms,killed,n):
    for false in range(1<<n):
        rows=killed+[sum(1<<j for j,t in enumerate(terms) if (t & 1<<i))
                     for i in range(n) if false>>i&1]
        semantic=any(all(not(r>>j&1) for r in rows) for j in range(len(terms)))
        compiled=any(s.bit_count()%2 for s in nullspace(rows,len(terms)))
        if semantic!=compiled: return False
    return True

if __name__=='__main__':
    count=0
    for n in range(4):
        for mask in range(1<<(1<<n)):
            terms=[i for i in range(1<<n) if mask>>i&1]
            assert fiber(terms,[],n)==brute(terms,[],n)
            count+=1
    rng=Random(1337)
    for _ in range(900):
        n=rng.randrange(7)
        t=rng.randrange(13)
        terms=[rng.randrange(1<<n) for j in range(t)]
        rows=[rng.randrange(1<<t) for _ in range(rng.randrange(5))]
        assert fiber(terms,rows,n)==brute(terms,rows,n)
    print(count,'raw unate families and 900 fixed-polarity fibers matched')

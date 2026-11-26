"""Check universality reduction using brute-force delta-parity as a stand-in for GIM."""
from itertools import combinations, permutations
from random import Random
from single_cycle_check import fixture,orbits,switch
from check_promise_pfaffian import passive,cap,settings

def rank(rows):
    basis={}
    for v in rows:
        while v and v.bit_length() in basis:v^=basis[v.bit_length()]
        if v:basis[v.bit_length()]=v
    return len(basis)
def bits(mask):
    return [i for i in range(mask.bit_length()) if mask>>i&1]
def nonsingular(A,I):
    return rank([A[i]&I for i in bits(I)])==I.bit_count()
def sub(A,indices):
    return [sum(((A[i]>>j)&1)<<b for b,j in enumerate(indices)) for i in indices]
def pivot(A,I):
    # Principal pivot transform on I, using a row-system dictionary:
    # old outputs Ay become new inputs on I.
    n=len(A);left=[];right=[]
    for i,row in enumerate(A):
        left.append((row&I) ^ ((1<<i) if not(I>>i&1) else 0))
        right.append((row&~I) ^ ((1<<i) if I>>i&1 else 0))
    for j in range(n):
        k=next(k for k in range(j,n) if left[k]>>j&1)
        for M in (left,right):M[k],M[j]=M[j],M[k]
        for i in range(n):
            if i!=j and left[i]>>j&1:left[i]^=left[j];right[i]^=right[j]
    return right

def raw(succ,chords):
    ref=list(succ);T=[]
    for ch in chords:
        lab,_=orbits(ref);t=lab[ch[0]]!=lab[ch[1]];T.append(t)
        if t:switch(ref,ch)
    _,paths=orbits(ref)
    if len(paths)!=1:return None
    pos={a:i for i,a in enumerate(paths[0])}
    ends=[sorted(pos[a] for a in ch) for ch in chords]
    B=[sum(int((a<c<b)^(a<d<b))<<j for j,(c,d) in enumerate(ends)) for a,b in ends]
    pairs=[]
    for i in range(0,len(chords),2):
        j=i+1
        if T[i]==T[j]:pairs.append((i,j))
        else:
            u=len(B);B.append(1<<i);B[i]|=1<<u;pairs.append((j,u))
    return B,pairs

def brute_delta(A,twist,pairs):
    for s in range(1<<len(pairs)):
        F=sum((1<<i)|(1<<j) for k,(i,j) in enumerate(pairs) if s>>k&1)
        if nonsingular(A,F^twist):return True
    return False

def can_include(C,i,j):
    T=[i,j];n=len(C)
    if rank([C[i],C[j]])<2:return False
    for k in range(n):
        if k not in T and rank([C[l] for l in [*T,k]])>len(T):T.append(k)
    twist=sum(1<<x for x in T);assert nonsingular(C,twist)
    keep=[l for l in range(n) if l not in (i,j)]
    D=sub(pivot(C,twist),keep)
    mask=sum((1<<k) for k,l in enumerate(keep) if l in T)
    return brute_delta(D,mask,[(k,k+1) for k in range(0,len(D),2)])

def is_universal_raw(B,pairs):
    M=list(B)
    for i,j in pairs:M[i]^=1<<j;M[j]^=1<<i
    kept=[i for pair in pairs for i in pair]
    U=sum(1<<i for i in range(len(M)) if i not in kept)
    if not nonsingular(M,U):return False
    C=sub(pivot(M,U),kept)
    return not any(can_include(C,2*i,2*i+1) for i in range(len(pairs)))

def is_universal(p,e):
    reduced=raw(p,e)
    return reduced is not None and is_universal_raw(*reduced)

def check():
    r=Random(12746); physical=0;solved=0;anchor=0
    for n in range(2,9):
        for trial in range(52):
            m=r.randrange(0,6) if n>=3 else 0
            gates=[r.sample(range(n),3) for _ in range(m)]
            p,e,last=fixture(n,gates,r.sample(range(n),n))
            k=r.randint(2,min(n,4)); loc=[last+i for i in r.sample(range(n),k)]
            a,b=[last+i for i in r.sample(range(n),2)]
            p,mks=passive(p,[*loc,a,b]);L=mks[:-2];a,b=mks[-2:]
            ts=settings(p,e); true=[orbits(t) for t in ts]
            if all(len(c)==2 for _,c in true):
                crossing=cap(p,[a,b])
                possible=not is_universal(crossing,e)
                assert possible==any(l[a]==l[b] for l,c in true)
                if possible:
                    old=list(p);new=list(crossing);rest=list(e)
                    while rest:
                        first,rest=rest[:2],rest[2:]
                        if is_universal(new,rest):
                            for ch in first:switch(new,ch);switch(old,ch)
                    l,_=orbits(old);assert l[a]==l[b];solved+=1
            allgood=True
            for order in permutations(range(k)):
                if order[0]:continue
                capmarks=[L[i] for i in order]
                C=cap(p,capmarks);got=is_universal(C,e)
                assert got==all(len(orbits(cap(t,capmarks))[1])==1 for t in ts)
                allgood &=got;physical+=1
            assert allgood==all(len(c)==k and len({l[u] for u in L})==k for l,c in true)
            anchor+=1
    for m in range(6):
        for trial in range(160):
            n=2*m+r.randrange(0,4);B=[0]*n
            for i in range(n):
                for j in range(i):
                    if r.randrange(2):B[i]|=1<<j;B[j]|=1<<i
            order=r.sample(range(n),n);pairs=list(zip(order[:2*m:2],order[1:2*m:2]))
            # Each monomial coefficient is the Pfaffian after deleting its tagged endpoints.
            all_indices=(1<<n)-1
            true=all(nonsingular(B,all_indices^sum((1<<i)|(1<<j) for k,(i,j) in enumerate(pairs) if s>>k&1))
                     for s in range(1<<m))
            assert true==is_universal_raw(B,pairs)
    print(physical,'physical cap identities;',anchor,'landmark recognitions;',solved,'joined witnesses; 960 arbitrary matrices')
if __name__=='__main__':check()

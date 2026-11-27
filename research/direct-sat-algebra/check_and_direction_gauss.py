"""Finite direction-sieve controls in native affine/AND circuits."""
from itertools import product
from random import Random
from check_and_count_low_precision_raw import arithmetic,direct
from check_and_star_gauss import affine,xorprod,signed
from quadratic_target import parity


def run(n,g,dirs,pins=(),gauge=True):
    gates,(out,c)=arithmetic(n,g)
    m=len(gates)
    P=affine(out,c)
    occupied=0
    shadows=[]
    for v in dirs:
        if not 0<v<1<<m:
            raise ValueError('invalid direction')
        N=sum(int(any(parity(a&(v<<n)) for a,b in pair))<<j for j,pair in enumerate(gates))
        if v&N or occupied&(v|N):
            raise ValueError('overlapping direction footprints')
        occupied|=v|N
        shadows.append((v,N))
        if gauge and (parity(out&(v<<n))^1^(v.bit_count()%2)):
            i=(v&-v).bit_length()-1
            a,b=gates[i]
            P^={1<<(n+i)}^xorprod(affine(*a),affine(*b))
    total=terms=0
    for U in range(1<<m):
        if any(U&v==v and not U&N for v,N in shadows):
            continue
        terms+=1
        phase=P.copy()
        eq=list(pins)
        for j,(a,b) in enumerate(gates):
            z=1<<(n+j)
            if U>>j&1:
                eq.extend([(a[0],1^a[1]),(b[0],1^b[1])])
                phase^={0,z}
            else:
                eq.append((z,0))
        total+=signed(phase,n+m,eq)
    volume=sum(all(parity(x&a)==b for a,b in pins) for x in range(1<<n))
    return (volume-total)//2,terms


def triples(k):
    n=3*k
    g=[]
    def emit(op,*args):
        g.append((op,args))
        return n+len(g)-1
    A=B=emit('xor')
    for block in range(k):
        z=[]
        for j in range(3):
            a=emit('xor',3*block+j,A)
            b=(2 if block==0 else B) if j==0 else emit('xor',B,z[j-1])
            z.append(emit('and',a,b))
        A=emit('xor',A,z[1])
        B=emit('xor',B,z[0],z[2])
    emit('xor',z[-1])
    return n,g


if __name__=='__main__':
    rng=Random(94)
    cases=0
    for k in (1,2,3):
        n,g=triples(k)
        for _ in range(5):
            pins=[(rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(3))]
            expected=sum(direct(n,g,x)[0] and all(parity(x&a)==b for a,b in pins) for x in range(1<<n))
            assert run(n,g,[5<<(3*j) for j in range(k)],pins)==(expected,7**k)
            cases+=1
    n,g=triples(1)
    for bad in ([5,2],[3]):
        try:
            run(n,g,bad)
        except ValueError:
            pass
        else:
            raise AssertionError('invalid overlap accepted')
    # A successor reads the invariant pair parity, which can defeat ungauged sieving.
    g=[('and',(0,0)),('and',(0,0)),('xor',(1,2)),('and',(3,0)),('one',(4,))]
    assert run(1,g,[3])==(2,6) and run(1,g,[3],gauge=False)[0]==0
    checked=0
    for _ in range(250):
        n=rng.randrange(1,5)
        g=[]
        for j in range(rng.randrange(2,8)):
            op=rng.choice(('and','and','xor','one'))
            g.append((op,tuple(rng.randrange(n+j) for i in range(2 if op=='and' else rng.randrange(3)))))
        pairs,_=arithmetic(n,g)
        dirs=list(range(1,1<<len(pairs)))
        rng.shuffle(dirs)
        pack=[]
        for v in dirs:
            if len(pack)==2: break
            try:
                run(n,g,pack+[v])
            except ValueError:
                continue
            pack.append(v)
        assert run(n,g,pack)[0]==sum(direct(n,g,x)[0] for x in range(1<<n))
        checked+=1
    print(cases,'triple-family pinned runs through k=3,',checked,'random raw counts, even-gauge and overlap controls passed')

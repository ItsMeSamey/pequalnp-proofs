"""Audit a concrete simultaneous-cut certificate and both refined-leaf charts."""
from itertools import combinations
from random import Random
from affine_cell_energy import AffineCellEnergy


def rank(rows):
    basis={}
    for x in rows:
        while x:
            i=x.bit_length()-1
            if i not in basis: basis[i]=x; break
            x ^= basis[i]
    return len(basis)


def sample(n,rng):
    while True:
        rows=[rng.getrandbits(n) for _ in range(n-2)]
        if rank(rows)==n-2:
            return rows


def chart(n,rows,other):
    cell=((rows[0],0),)
    terms=[]
    for v in other:
        terms.append((1,cell+((v,1),)))
        cell+=((v,0),)
    terms.append((1,cell))
    terms.extend((1,((v,0),)) for v in rows[1:])
    assert rank(m for _,flat in terms for m,_ in flat)==len(rows)+len(other)
    energy=AffineCellEnergy(n,terms)
    stack=[(0,0,())];queries=0;actual=set()
    while stack:
        j,z,f=stack.pop();queries+=1
        if not energy.energy(f):continue
        if j==n:
            actual.add(z);continue
        for b in (0,1):
            stack.append((j+1,z|(b<<j),f+((1<<j,b),)))
    assert actual=={0,*rows} and queries<=1+2*n*(1+len(rows))


if __name__=='__main__':
    rng=Random(8092)
    small=sample(12,rng)
    for B in combinations(range(12),6):
        bm=sum(1<<j for j in B)
        freq=[z&bm for z in small]
        good=[row for row,mask in zip(small,freq) if mask and freq.count(mask)==1]
        assert rank(row & ~bm for row in good)>=2
    small8=sample(8,rng)
    chart(8,small8[:3],small8[3:]);chart(8,small8[3:],small8[:3])
    n=128;rows=sample(n,Random(71));full=(1<<n)-1
    zeros=[full^r for r in rows]+[full^a^b for a,b in combinations(rows,2)]
    assert all((u&v).bit_count()<n//2 for u,v in combinations(zeros,2))
    print(f'Certified rank {len(rows)} in 128 variables across every balanced cut via {len(zeros)*(len(zeros)-1)//2} pair tests; 924 small cuts and both refined charts passed')

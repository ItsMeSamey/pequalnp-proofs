"""Independent upper-space verifier for degree-three multilinear PC over GF(2).

Uses sparse sets of monomial masks. For each variable, forms its entire
multiplication image on the supplied space. A degree-first echelon basis of
that image identifies all the image vectors admissible at degree three.
"""
import json
from pathlib import Path

def lead(q):
    return max(q,key=lambda m:(m.bit_count(),m))

def reduce_row(q,basis):
    while q:
        h=lead(q)
        if h not in basis:
            break
        q=q^basis[h]
    return q

def echelon(rows):
    piv={}
    for row in rows:
        q=reduce_row(row,piv)
        if q:piv[lead(q)]=q
    return piv

def mulvar(q,var):
    out=set()
    for m in q:
        u=m|var
        if u in out:out.remove(u)
        else:out.add(u)
    return frozenset(out)

def add(*parts):
    q=frozenset()
    for p in parts:q=q^frozenset(p)
    return q

def bits(x):
    return (i for i in range(x.bit_length()) if x>>i&1)

def verify_space(path,target):
    c=json.loads(Path(__file__).with_name(path).read_text())
    rows=c['matrix'];n=len(rows);offset=c['offset'];marker=c['marker']
    assert all(0<=v<1<<n for v in rows)
    space=[]
    for clause in c['space_basis']:
        assert len(clause)==len(set(clause)) and all(0<=m<1<<n and m.bit_count()<=3 for m in clause)
        space.append(frozenset(clause))
    basis=echelon(space)
    assert len(basis)==len(space)
    def contains(q):return not reduce_row(frozenset(q),basis)
    for i,row in enumerate(rows):
        affine=add([1<<j for j in bits(row)], [0] if offset>>i&1 else [])
        assert contains(mulvar(affine,1<<i)), ('missing pivot',i)
    if marker is not None:
        assert contains(add([0],[1<<j for j in bits(marker)])), 'missing marker'
    assert not contains(target), 'target is inside proposed obstruction'
    for i in range(n):
        image=echelon(mulvar(q,1<<i) for q in space)
        for pivot,entry in image.items():
            if pivot.bit_count()<=3:
                assert contains(entry), ('nonclosed',i,pivot)
    print(path,':',len(space),'independent rows, axioms and all multiplication images verified')
    return rows,offset,marker

def lift(M,b,l,c):
    t=1<<len(M)
    return [v+(t if c>>i&1 else 0) for i,v in enumerate(M)]+[l],(b^c)|t,t

if __name__=='__main__':
    if not __debug__:
        raise SystemExit('Run without Python optimization so every assertion is checked.')
    n=11
    rows,b,marker=verify_space('affine-base.json',{1<<(n-1)})
    assert marker is None
    # Start with the six implications around a cycle. Its only models are
    # constant, so the xor of coordinates 0 and 3 vanishes. Each lift gives
    # a new pivot t; t=1 recovers the old instance and demands old xor = 1.
    lifted=([1<<((i+1)%6) for i in range(6)],63,9)
    for c in [0,10,1,16,128]:lifted=lift(*lifted,c)
    assert lifted==(rows,b,1<<(n-1))
    models=[x for x in range(1<<n) if all(((rows[i]&x).bit_count()&1)==(b>>i&1) for i in bits(x))]
    assert len(models)==38 and all(not (x>>(n-1)&1) for x in models)
    M,B,L=verify_space('unsat-marker.json',{0})
    assert M==rows+[v<<n for v in rows]
    assert B==b|(b<<n) and L==(1<<(n-1))|(1<<(2*n-1))
    print('The 22-variable marker is impossible on every pair of the 38 local models.')
    proof=json.loads(Path(__file__).with_name('degree4-proof.json').read_text())
    values=[]
    for op,x,*others in proof:
        if op=='a':
            assert not others and 0<=x<n
            v=mulvar(add([1<<j for j in bits(rows[x])],[0] if b>>x&1 else []),1<<x)
        elif op=='+':
            y,=others
            assert 0<=x<len(values) and 0<=y<len(values)
            v=values[x]^values[y]
        else:
            assert op=='*'
            y,=others
            assert 0<=x<len(values) and 0<=y<n
            assert all(t.bit_count()<=3 for t in values[x])
            v=mulvar(values[x],1<<y)
        assert all(t.bit_count()<=4 for t in v)
        values.append(v)
    assert values[-1]=={1<<(n-1)}
    print('Verified',len(values),'degree-four PC lines deriving the forced bit.')

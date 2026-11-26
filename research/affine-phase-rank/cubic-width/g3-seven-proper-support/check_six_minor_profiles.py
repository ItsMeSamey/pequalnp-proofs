"""Exact integer support-packing sieve for six full signs on the six-bit cubic minor."""
from itertools import combinations_with_replacement, product
from math import gcd


def rank(rows):
    basis = {}
    for original in rows:
        row = list(original)
        for j, pivot in sorted(basis.items()):
            row = [pivot[j]*x-row[j]*y for x,y in zip(row,pivot)]
            scale=gcd(*row)
            if scale: row=[x//scale for x in row]
        j=next((j for j,v in enumerate(row) if v),None)
        if j is not None: basis[j]=row
    return len(basis)


def bound(rows,values):
    n=len(rows)
    full=(1<<n)-1
    values_mask=sum((v<0)<<i for i,v in enumerate(values))
    parities=set()
    for mask in range(32):
        mask <<= 1
        h=sum((sum(v<0 for j,v in enumerate(row) if mask>>j&1)%2)<<i for i,row in enumerate(rows))
        parities.update((h,full^h))
    weights={}
    for h in parities:
        if h and rank([row for i,row in enumerate(rows) if not h>>i&1])<6:
            weights[h]=16
        t=h^values_mask
        if not t:return 65
        weights[t]=max(weights.get(t,0),14)
    packs={0:0}
    for mask,w in weights.items():
        for taken,v in list(packs.items()):
            if not mask&taken: packs[mask|taken]=max(packs.get(mask|taken,0),v+w)
    return max(packs.values())


def check():
    candidates=[(1,)+bits for bits in product((1,-1),repeat=5)]
    survivors=[]
    for denominator in (2,4,6):
        for weights in combinations_with_replacement(range(1,7),6):
            if gcd(denominator,*weights)!=1:continue
            if denominator!=4 and sum(v%2 for v in weights)<5:continue
            pairs=[(row,sum(a*s for a,s in zip(weights,row))) for row in candidates]
            pairs=[(row,val) for row,val in pairs if abs(val)==denominator]
            if rank([row for row,val in pairs])<6:continue
            rows,values=zip(*pairs)
            required=bound(rows,values)
            print(denominator,weights,len(pairs),required)
            if required<=64:survivors.append((denominator,weights))
    assert survivors==[(2,(1,1,1,1,1,1)),(2,(1,1,1,1,1,3))]

if __name__=='__main__':check()

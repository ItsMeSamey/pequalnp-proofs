"""Test block inclusion-exclusion, varying witness-slice weights, and scalar rank."""
from fractions import Fraction
from itertools import product

def rank(rows):
    rows=[list(map(Fraction,r)) for r in rows]
    n=len(rows)
    for i in range(n):
        p=next((j for j in range(i,n) if rows[j][i]),None)
        if p is None:
            return False
        rows[i],rows[p]=rows[p],rows[i]
        for j in range(i+1,n):
            if rows[j][i]:
                c=rows[j][i]/rows[i][i]
                rows[j]=[a-c*b for a,b in zip(rows[j],rows[i])]
    return True

for n in range(1,6):
    for width in range(1,n+1):
        blocks=[range(i,min(i+width,n)) for i in range(0,n,width)]
        terms=[]
        for block in blocks:
            for sub in range(1,1<<len(block)):
                terms.append((sum(1<<k for j,k in enumerate(block) if sub>>j&1),
                              (-1)**(1+sub.bit_count())))
        levels=set()
        pooled={}
        # For each z use differently scaled scores; expand the zero-test polynomial.
        for z in (1,2,3):
            coeff={0:Fraction(1)}
            for j in range(1,len(blocks)+1):
                nxt=coeff.copy()
                for mask,c in coeff.items():
                    for m,w in terms:
                        k=mask|m
                        nxt[k]=nxt.get(k,0)-c*z*w/Fraction(j*z)
                coeff=nxt
            for mask,c in coeff.items():
                pooled[mask]=pooled.get(mask,0)+c
        matrix=[]
        for x in range(1<<n):
            row=[]
            for y in range(1<<n):
                score=sum(w for m,w in terms if x&y&m==m)
                levels.add(score)
                val=sum(c for m,c in pooled.items() if x&y&m==m)
                assert score==sum(any(x&y&(1<<k) for k in b) for b in blocks)
                assert val==3*int(not x&y)
                row.append(val)
            matrix.append(row)
        assert levels==set(range(len(blocks)+1)) and rank(matrix)
print('15 block layouts, pooled coefficients across three witness slices, full ranks passed')

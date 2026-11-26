from itertools import combinations, permutations, product
from random import Random
rng=Random(2893)
def det(M):
    rows=[sum(v<<j for j,v in enumerate(row)) for row in M]
    for j in range(len(rows)):
        pivot=next((i for i in range(j,len(rows)) if rows[i]>>j&1),None)
        if pivot is None:return 0
        rows[j],rows[pivot]=rows[pivot],rows[j]
        for i in range(j+1,len(rows)):
            if rows[i]>>j&1:rows[i]^=rows[j]
    return 1
def sum_forms(M,c):
    p=len(c); d=len(M[0]); k=p-d
    def select(start,rows,mult,left):
        if not left:
            cols=[j for j in range(d) if j not in mult]
            return det([[M[i][j] for j in cols] for i in rows]) if len(rows)==len(cols) else 0
        ans=0
        for j in range(start,d):
            for sz in range(2,left+2):
                for block in combinations(rows,sz):
                    if all(M[i][j] for i in block):
                        ans ^= select(j+1,[i for i in rows if i not in block],mult+[j],left-sz+1)
        return ans
    ans=0
    for n in range(k+1):
        for fixed in combinations(range(p),n):
            if all(c[i] for i in fixed):
                ans ^= select(0,[i for i in range(p) if i not in fixed],[],k-n)
    return ans
checks=0
for p in range(1,8):
    for d in range(max(0,p-3),p+1):
        for _ in range(50):
            M=[[rng.randrange(2) for j in range(d)] for i in range(p)]
            c=[rng.randrange(2) for i in range(p)]
            total=sum(all((c[i]+sum(a*b for a,b in zip(row,x)))%2 for i,row in enumerate(M)) for x in product(range(2),repeat=d))%2
            assert sum_forms(M,c)==total
            checks+=1
print(checks,'kernel evaluations through deficit three passed')

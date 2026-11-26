"""Exhaustive square matrices through order four, plus seeded larger matrices."""
from itertools import product
from random import Random

def det(rows):
    m = [list(row) for row in rows]
    d, sign = 1, 1
    for i in range(len(m)-1):
        pivot = next((j for j in range(i,len(m)) if m[j][i]), None)
        if pivot is None:
            return 0
        if pivot != i:
            m[i],m[pivot] = m[pivot],m[i]
            sign = -sign
        for j in range(i+1,len(m)):
            for k in range(i+1,len(m)):
                m[j][k] = (m[i][i]*m[j][k]-m[i][k]*m[j][i])//d
        d = m[i][i]
    return sign*m[-1][-1]

def check(rows):
    n = len(rows)
    value = det(rows)
    if value%2:
        assert value**2%8 == 1
        return
    total = 0
    for i,row in enumerate(rows):
        minors = []
        for k,bit in enumerate(row):
            if bit:
                minors.append(det([r[:k]+r[k+1:] for j,r in enumerate(rows) if j!=i])%2)
        ones = sum(minors)
        total += ones*(ones-1)//2
    assert value**2%8 == 4*(total%2), rows

if __name__ == '__main__':
    count=0
    for n in (2,3,4):
        for bits in product((0,1), repeat=n*n):
            check([bits[i:i+n] for i in range(0,len(bits),n)])
            count += 1
    rand=Random(1456)
    for n in (5,6,7):
        for _ in range(600):
            check([tuple(rand.randrange(2) for _ in range(n)) for _ in range(n)])
            count+=1
    print(count,'coefficient checks passed')

"""Small direct controls for signed offset-class rank factorization."""
from itertools import product
from random import Random

def decompose(matrix, prime):
    residual = [row[:] for row in matrix]
    terms = []
    while True:
        pivot = next(((i,j) for i,row in enumerate(residual)
                      for j,value in enumerate(row) if value), None)
        if pivot is None:
            return terms
        i,j = pivot
        inverse = pow(residual[i][j], -1, prime)
        left = [row[j] for row in residual]
        right = [(x*inverse) % prime for x in residual[i]]
        terms.append((left,right))
        residual = [[(x-left[u]*right[v]) % prime for v,x in enumerate(row)]
                    for u,row in enumerate(residual)]

def transform(values, prime):
    table = list(values)
    width = 1
    while width < len(table):
        for start in range(0,len(table),2*width):
            for j in range(start,start+width):
                a,b = table[j],table[j+width]
                table[j],table[j+width] = (a+b)%prime,(a-b)%prime
        width *= 2
    return table

def flag(bits, part, n, q):
    return [bits[i]^part if i<n else 0 for i in range(q)]

def check(n, clauses):
    q = 1 << (n-1).bit_length()
    prime = {4:5,8:11}[q]
    matrices = {}
    for (i,j,k), signs in clauses:
        key = (signs,i^j^k)
        matrix = matrices.setdefault(key,[[0]*q for _ in range(q)])
        matrix[i][j] = 1
    groups = [(signs,offset,decompose(m,prime)) for (signs,offset),m in matrices.items()]
    for bits in product((0,1), repeat=n):
        direct = not any(all(bits[index]^sign for index,sign in zip(sites,signs))
                         for sites,signs in clauses)
        valid = True
        for signs,offset,terms in groups:
            a,b,c = (flag(bits,s,n,q) for s in signs)
            c = transform(c,prime)
            rows = [0]*q
            for left,right in terms:
                field_b = transform([v*bit for v,bit in zip(right,b)],prime)
                convolution = transform([u*v for u,v in zip(field_b,c)],prime)
                for i in range(q):
                    rows[i] += left[i]*convolution[i^offset]
            # The field Walsh return is q times the group convolution.
            valid &= not any(a[i] and rows[i]%prime for i in range(q))
        assert direct == valid
    return 1<<n

if __name__ == '__main__':
    rng = Random(1729)
    tested = 0
    for n in (3,4,5):
        for _ in range(16):
            clauses = [(tuple(rng.randrange(n) for _ in range(3)),
                        tuple(rng.randrange(2) for _ in range(3))) for _ in range(12)]
            tested += check(n,clauses+clauses[:2])
    print(f'{tested} original assignments checked')

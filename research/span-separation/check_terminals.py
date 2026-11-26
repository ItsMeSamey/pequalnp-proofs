from itertools import combinations, product
from exchange import eliminate, represent


def instance(n, edges):
    w = 1 << (2*n)
    expressions = [(1 << (2*i), 1 << (2*i+1)) for i in range(n)]
    for i,j in edges:
        expressions.append((w ^ (1 << (2*i)) ^ (1 << (2*j)),
                            w ^ (1 << (2*i+1)) ^ (1 << (2*j+1))))
    ordinary = []
    kernel = []
    target = 0
    for block, pair in enumerate(expressions):
        first = 2*n+1+3*block
        tip = 1 << first
        target ^= tip
        for side, expr in enumerate(pair):
            arm = 1 << (first+1+side)
            ordinary.extend((arm, arm ^ tip))
            kernel.append(arm ^ expr)
    kernel.append(target)
    return ordinary,kernel,target,w,2*n+1+3*len(expressions)


def annihilator_generator(kernel, dim):
    pivots = eliminate(kernel)
    for free in range(dim):
        if free in pivots:
            continue
        vector = 1 << free
        for p,(row,_) in sorted(pivots.items()):
            if (row & vector).bit_count() & 1:
                vector ^= 1 << p
        yield vector


def general_solver(ordinary, kernel, target, w, dim):
    directions = list(annihilator_generator(kernel, dim))
    phi = 0
    for step in range(1 << len(directions)):
        if step:
            phi ^= directions[(step & -step).bit_length()-1]
        if not ((phi & w).bit_count() & 1):
            continue
        zero = [col for col in ordinary if (col & phi).bit_count()%2 == 0]
        if represent(eliminate(zero),target) is not None:
            assert represent(eliminate(zero+kernel),w) is None
            return True
    return False


def check():
    cases = 0
    for n in range(1,5):
        pairs = list(combinations(range(n),2))
        for mask in range(1 << len(pairs)):
            edges = [ep for i,ep in enumerate(pairs) if mask >> i & 1]
            colorable = any(all(c[i]!=c[j] for i,j in edges)
                            for c in product(range(3),repeat=n))
            assert general_solver(*instance(n,edges)) == colorable, (n,edges)
            cases += 1
    print('Verified',cases,'labeled graphs by generic binary separator enumeration.')

if __name__ == '__main__':
    check()

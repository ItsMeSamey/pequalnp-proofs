"""Direct local-signature and independent full weighted host controls."""
from itertools import combinations, product
from pathlib import Path
import runpy

single = runpy.run_path(str(Path(__file__).with_name('check-weighted-permutation.py')))
put_star, tree_weight, P = (single[name] for name in ('put_star','tree_weight','P'))


def layers(n):
    a = tuple(range(n+1))
    c = tuple(range(n+1,2*n+2))
    middle = [tuple(range(2*n+2+4*j,2*n+6+4*j)) for j in range(n)]
    left = [((i,j),(a[i],a[i+1],*middle[j][:2])) for i in range(n) for j in range(n)]
    right = [((j,k),(*middle[j][2:],c[k],c[k+1])) for j in range(n) for k in range(n)]
    return a,c,middle,left,right


def literal_one(x,L,M,R):
    a,c,middle,left,right = layers(1)
    edges = []
    cells = [(left[0][1],L*x),(middle[0],M),(right[0][1],R)]
    for index,(ports,weight) in enumerate(cells):
        put_star(edges,ports,8+index,weight)
    vertices = set(range(11))
    free = sorted(vertices-set(a)-set(c))
    result = 0
    for mask in range(1<<len(free)):
        red = set(a) | {v for j,v in enumerate(free) if mask>>j&1}
        result += tree_weight(edges,red)*tree_weight(edges,vertices-red)
    return result % P


def pure_coefficient(n, cells):
    a,c,*_ = layers(n)
    red = (1<<a[0])|(1<<a[-1])
    blue = (1<<c[0])|(1<<c[-1])
    states = {tuple(1<<i for i in range(6*n+2)):1}
    for t,cell in enumerate(cells):
        next_states = {}
        future = red|blue
        for other in cells[t+1:]:
            for v in other:
                future |= 1<<v
        for before,w in states.items():
            for cut in range(1,15,2):
                blocks = list(before)
                for bit in (0,1):
                    members = [v for j,v in enumerate(cell) if (cut>>j)&1==bit]
                    pieces = [next(b for b in blocks if b>>v&1) for v in members]
                    if len(set(pieces)) < len(pieces):
                        break
                    new = sum(pieces)
                    if (new & red) and (new & blue):
                        break
                    blocks = [b for b in blocks if b not in pieces]+[new]
                else:
                    if all(b&future for b in blocks):
                        key = tuple(sorted(blocks))
                        sign = 1 if cut.bit_count()==2 else -1
                        next_states[key] = next_states.get(key,0)+sign*w
        states = {s:w for s,w in next_states.items() if w}
    return sum(w for blocks,w in states.items() if len(blocks)==2 and
               any(b&red==red for b in blocks) and any(b&blue==blue for b in blocks))


for x in (2,17,39):
    # On order one the grove is degree at most two in each of L,M,R.
    result = sum(L*M*R*literal_one(x,L,M,R) for L,M,R in product((-1,1),repeat=3))
    assert result*pow(8,-1,P)%P == 4*x%P
print('N=1: 24 literal signed-host values; three trivariate coefficient checks modulo 101')

for n in (1,2):
    a,c,middle,left,right = layers(n)
    left_coefficients = {}
    checks = 0
    for one in combinations(left,n):
        cells_l = [v for ij,v in one]
        cols_l = tuple(ij for ij,v in one)
        total = 0
        for two in combinations(right,n):
            cols_r = tuple(jk for jk,v in two)
            value = pure_coefficient(n,cells_l+middle+[v for jk,v in two])
            valid = all(len({p[i] for p in seq})==n for seq in (cols_l,cols_r) for i in (0,1))
            expected = (4 if n==1 else 32) if valid else 0
            assert value == expected, (cols_l,cols_r,value,expected)
            total += value
            checks += 1
        left_coefficients[cols_l] = total
    print(f'N={n}: {checks} layer-support pairs; nonzero monomials',
          {indices:v for indices,v in left_coefficients.items() if v})

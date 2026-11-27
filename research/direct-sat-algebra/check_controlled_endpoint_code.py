from random import Random
from controlled_endpoint_code import solve
from check_controlled_code_blocks import apply, legal, triangle, triangle_reference

rng = Random(2841)
for _ in range(500):
    m, n, k = [rng.randrange(6) for _ in range(3)]
    A = [rng.randrange(1 << m) for _ in range(n)]
    b = rng.randrange(1 << m)
    U = [rng.randrange(1 << m) for _ in range(k)]
    forms = [(rng.randrange(1 << n), rng.randrange(2)) for _ in U]
    count = sum(legal(A,b,U,forms,x,y) for x in range(1<<k) for y in range(1<<n))
    result = solve(m,A,b,U,forms)
    assert count == result.count and bool(count) == (result.witness is not None)
    if count:
        assert legal(A,b,U,forms,*result.witness)
    if result.codimension:
        assert solve(m,A,b,U,forms,max_codimension=result.codimension-1).status == "UNKNOWN"

for length in (1, 4, 14):
    m,A,b,U,forms,_ = triangle(length)
    # Reversible dense output and data transvections, affine data shift,
    # and control permutation retain the count without retaining obvious labels.
    for _ in range(8*m):
        i,j=rng.sample(range(m),2)
        def op(x):
            return x ^ (((x>>j)&1)<<i)
        A, b, U = list(map(op,A)), op(b), list(map(op,U))
    for _ in range(8*len(A)):
        i,j=rng.sample(range(len(A)),2)
        A[j] ^= A[i]
        forms = [(f ^ (((f>>i)&1)<<j), c) for f,c in forms]
    shift = rng.randrange(1<<len(A))
    b ^= apply(A,shift)
    forms = [(f,c^((f&shift).bit_count()%2)) for f,c in forms]
    order = rng.sample(range(m),m)
    U,forms=[U[i] for i in order],[forms[i] for i in order]
    result=solve(m,A,b,U,forms,max_codimension=0,max_width=2)
    assert result.count==triangle_reference(length) and legal(A,b,U,forms,*result.witness)
    assert solve(m,A,b,U,forms,max_width=1).status=="UNKNOWN"
# q fixed zero, one variable w appears twice: loop forbids w=1.
assert solve(0,[],0,[0],[(0,0)]).count==2
# q fixed one gives opposite copies of a common class, both feasible.
assert solve(0,[],0,[0],[(0,1)]).count==2
# q=0, w=1 forced: constant forbidden pair; linear code itself nonempty.
assert solve(1,[],1,[1],[(0,0)]).status=="UNSAT"
print("500 brute-force pencils; 3 densely recoded signed chains; caps, loops, constants passed")

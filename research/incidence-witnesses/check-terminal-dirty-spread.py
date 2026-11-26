"""Exact quadratic mincut checks for the 69-step pin-spread schedule."""
N, k, q = 161203, 402, 401
runs = [(4,27),(5,14),(6,8),(7,5),(8,4),(9,2),(10,2),(11,1),
        (12,1),(13,1),(14,1),(16,1),(19,1),(25,1)]
z = steps = max_batch = 0
for d, count in runs:
    for _ in range(count):
        lost = 0
        for a in range(1, z+1):
            overlaps = min(max((a*(a-1)+b-1)//b, b*(a-b)+b-1)
                           for b in range(1, min(a, steps+max_batch-1)+1))
            lost = max(lost, k*a-overlaps)
        m = N-lost
        target = 646425*d//(d+1)+1
        assert d+z <= 401 and target <= d*m
        lo = m-(target-1)//d
        alpha = k*m-N*d
        beta = N*(d*m-target+1)
        gamma = q*m*(N-m)
        turn = -(2*alpha*beta-gamma*N)//(2*(alpha**2+gamma))
        for u in (lo, m, turn, turn+1):
            if lo <= u <= m:
                w = alpha*u+beta
                assert w > 0 and w*w > gamma*u*(N-u)
        steps += 1
        z += d-1
        max_batch = max(max_batch, d-1)
assert (steps,z)==(69,372)
print(steps,z)

"""Weighted determinant moments on a scaled quadratic-subfield line."""
from additive_slope_prefix import _det


def carry_patterns(a, residue):
    """Yield repeat counts u with sum u_i 2^i = residue modulo 2^a-1."""
    if a < 1:
        raise ValueError("positive half degree required")
    residue %= (1 << a) - 1
    for start in range(3):
        viable = [{start}]
        for i in reversed(range(a)):
            bit = (residue >> i) & 1
            viable.append({c for c in range(3) if any(
                0 <= bit + 2*dest - c <= 2 for dest in viable[-1])})
        if start not in viable[-1]:
            continue
        path = []
        stack = [(start, iter(viable[a-1]))]
        while stack:
            i = len(path)
            carry, choices = stack[-1]
            dest = next(choices, None)
            if dest is None:
                stack.pop()
                if path:
                    path.pop()
                continue
            repeats = ((residue >> i) & 1) + 2*dest - carry
            if not 0 <= repeats <= 2:
                continue
            path.append(repeats)
            if i+1 == a:
                yield tuple(path)
                path.pop()
            else:
                stack.append((dest, iter(viable[a-i-2])))


class HalfLineMoments:
    """Sum det(D+diag((lambda*t)^(2^i))) t^r over nonzero subfield t."""
    def __init__(self, field, alternating_matrix, representative):
        d = field.m
        if d%2 or not 0 < representative < field.size:
            raise ValueError("even degree and nonzero scale required")
        if len(alternating_matrix)!=d or any(len(row)!=d for row in alternating_matrix):
            raise ValueError("wrong matrix shape")
        D = tuple(tuple(row) for row in alternating_matrix)
        if any(D[i][i] or any(D[i][j]!=D[j][i] for j in range(i)) for i in range(d)):
            raise ValueError("matrix must be alternating")
        self.f, self.a, self.D = field, d//2, D
        weights = [representative]
        for _ in range(1,d):
            weights.append(field.mul(weights[-1],weights[-1]))
        self.paired = [field.mul(weights[i],weights[i+self.a]) for i in range(self.a)]
        self.singleton = [((i,field.sqrt(weights[i+self.a])),
                           (i+self.a,field.sqrt(weights[i]))) for i in range(self.a)]

    def moment(self,r):
        if type(r) is not int:
            raise ValueError("integer moment required")
        f, a, D = self.f, self.a, self.D
        total = 0
        for pattern in carry_patterns(a,-r):
            if sum(pattern)%2:
                continue
            cols = []
            factor = 1
            for i,u in enumerate(pattern):
                if u == 0:
                    cols.extend([((i,1),), ((i+a,1),)])
                elif u == 1:
                    cols.append(self.singleton[i])
                else:
                    factor = f.mul(factor,self.paired[i])
            small = [[0]*len(cols) for _ in cols]
            for i,col in enumerate(cols):
                for j in range(i):
                    entry = 0
                    for p,v in col:
                        for q,w in cols[j]:
                            entry ^= f.mul(f.mul(v,w),D[p][q])
                    small[i][j] = small[j][i] = entry
            total ^= f.mul(factor,_det(f,small))
        return total

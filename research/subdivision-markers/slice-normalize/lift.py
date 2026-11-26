"""Polynomial-size alternating lift preserving the full projected witness set."""
from dataclasses import dataclass
from itertools import combinations
from solver import affine_chart, normalize, parity, quadratic


def products(matrix, equations):
    """Write q on the given nonempty fiber as <= half polar rank + 1 products."""
    chart = affine_chart(len(matrix),equations)
    if chart is None:
        raise ValueError('inconsistent marker equations')
    base,dirs,free = chart
    d = len(free)
    const = quadratic(matrix,base)
    linear = sum((quadratic(matrix,base^v)^const)<<i for i,v in enumerate(dirs))
    B = [0]*d
    for i,u in enumerate(dirs):
        for j in range(i):
            if quadratic(matrix,base^u^dirs[j]) ^ const ^ (linear>>i&1) ^ (linear>>j&1):
                B[i] |= 1<<j
                B[j] |= 1<<i
    pairs = []
    while any(B):
        i = next(i for i,row in enumerate(B) if row)
        j = (B[i]&-B[i]).bit_length()-1
        p,s = B[i],B[j]
        pairs.append((p,s))
        linear ^= p&s
        for k in range(d):
            if p>>k&1:
                B[k] ^= s
            if s>>k&1:
                B[k] ^= p
    one = next((mask for mask,h in equations if h),0)
    def ambient(v):
        return sum(1<<free[i] for i in range(d) if v>>i&1)
    result = [(ambient(p),ambient(s)) for p,s in pairs]
    # For a nonhomogeneous fiber, absorb any linear residual in the polar row space.
    if pairs:
        generators = [v for pair in pairs for v in pair]
        fit = affine_chart(len(generators), [
            (sum(((v>>j)&1)<<i for i,v in enumerate(generators)), (linear>>j)&1)
            for j in range(d)])
        if fit is not None and one:
            coeff = fit[0]
            for i,(p,s) in enumerate(result):
                a,b = (coeff>>(2*i+1))&1, (coeff>>(2*i))&1
                result[i] = p^(a*one), s^(b*one)
                const ^= a*b
            linear = 0
        elif fit is not None:
            # In a homogeneous chart, pair anisotropic two-planes without affine shifts.
            result = []
            anisotropic = []
            for i,(p,s) in enumerate(pairs):
                a,b = (fit[0]>>(2*i))&1, (fit[0]>>(2*i+1))&1
                if a and b:
                    anisotropic.append((p,s))
                else:
                    u,v = (p,p^s) if a else ((s,p^s) if b else (p,s))
                    result.append((ambient(u),ambient(v)))
            linear = 0
            for i in range(0,len(anisotropic)-1,2):
                p,s = anisotropic[i]
                u,v = anisotropic[i+1]
                result.extend([(ambient(s^u),ambient(p^u)),
                               (ambient(p^s^u^v),ambient(p^s^v))])
            if len(anisotropic)%2:
                p,s = anisotropic[-1]
                result.append((ambient(p),ambient(s)))
                linear = p^s
    assert one or not const
    leftover = ambient(linear) ^ (const*one)
    if leftover:
        result.append((leftover,leftover))
    return result,len(pairs)


@dataclass
class Lift:
    graph: list
    equations: list
    n: int
    factors: list
    gadget: str

    def repair(self,x):
        """Extend an original witness; raise ValueError for a nonwitness."""
        c = len(self.factors)
        if x < 0 or x >= 1<<self.n:
            raise ValueError('assignment exceeds original variable count')
        y = x
        for j,(_,v) in enumerate(self.factors):
            y |= parity(v&x) << (self.n+j)
        if any(parity(y&m)!=b for m,b in self.equations):
            raise ValueError('assignment violates a marker')
        if any(x>>i&1 and parity(row&y) for i,row in enumerate(self.graph[:self.n])):
            raise ValueError('assignment violates an original guard')
        odd = [j for j in range(c) if y>>(self.n+j)&1 and parity(self.graph[self.n+j]&y)]
        assert len(odd)%2==0
        if self.gadget == 'hub':
            if odd:
                y |= 1 << (self.n+2*c)
                for j in odd:
                    y |= 1 << (self.n+c+j)
            return y
        wanted = set(zip(odd[::2],odd[1::2]))
        for k,pair in enumerate(combinations(range(c),2)):
            if pair in wanted:
                y |= 1<<(self.n+c+k)
        return y


def build(matrix,equations,gadget="auto"):
    n = len(matrix)
    factors,_ = products(matrix,equations)
    c = len(factors)
    corrected = list(matrix)
    for u,v in factors:
        for i in range(n):
            if u>>i&1:
                corrected[i] ^= v
    graph = normalize(corrected,equations)
    assert graph is not None
    if gadget == 'auto':
        gadget = 'pairs' if c*(c-1)//2 <= c+1 else 'hub'
    if gadget not in ('pairs','hub'):
        raise ValueError("unknown repair gadget")
    extra = c*(c-1)//2 if gadget == 'pairs' else c+1
    graph.extend([0]*(c+extra))
    markers = list(equations)
    for j,(u,v) in enumerate(factors):
        z = n+j
        graph[z] = u
        for i in range(n):
            if u>>i&1:
                graph[i] |= 1<<z
        markers.append((v | (1<<z),0))
    if gadget == 'hub':
        hub = n+2*c
        for i in range(c):
            w = n+c+i
            graph[w] = (1<<(n+i))|(1<<hub)
            graph[n+i] |= 1<<w
            graph[hub] |= 1<<w
        return Lift(graph,markers,n,factors,gadget)
    for k,(i,j) in enumerate(combinations(range(c),2)):
        w = n+c+k
        graph[w] = (1<<(n+i))|(1<<(n+j))
        graph[n+i] |= 1<<w
        graph[n+j] |= 1<<w
    return Lift(graph,markers,n,factors,gadget)

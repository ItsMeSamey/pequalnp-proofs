"""Deterministic witness and cyclic-kernel charts for fixed-support product fibers."""
from dataclasses import dataclass
from math import gcd
from quadratic_target import affine_domain


@dataclass(frozen=True)
class Component:
    vertices: tuple
    exponents: tuple
    order: int


@dataclass(frozen=True)
class Basepoint:
    values: tuple
    components: tuple


def solve(field,n,edges,support):
    """Edges (i,j,t,b) impose x_i F^t(x_j)=b. Support is an iterable of indices."""
    edges = tuple(edges)
    active = set(support)
    if n < 0 or any(type(i) is not int or not 0<=i<n for i in active):
        raise ValueError("invalid support")
    m = field.m
    order = field.size-1

    def frob(x,t):
        for _ in range(t % m):
            x = field.mul(x,x)
        return x

    def div(x,y):
        return field.mul(x,field.inverse(y))

    adjacent = [[] for _ in range(n)]
    for j,(u,v,t,b) in enumerate(edges):
        if not (0<=u<n and 0<=v<n and isinstance(t,int) and 0<=b<field.size):
            raise ValueError("invalid edge")
        if bool(b) != (u in active and v in active):
            return None
        if b:
            adjacent[u].append((j,v,True))
            adjacent[v].append((j,u,False))

    answer = [0]*n
    components = []
    expressions = {}
    for root in sorted(active):
        if root in expressions:
            continue
        expressions[root] = (1,0,1)
        stack = [root]
        vertices = []
        extras = []
        visited_edges = set()
        while stack:
            u = stack.pop()
            vertices.append(u)
            a,s,sign = expressions[u]
            for j,v,forward in adjacent[u]:
                if j in visited_edges:
                    continue
                visited_edges.add(j)
                _,_,t,b = edges[j]
                if v in expressions:
                    extras.append(j)
                else:
                    if forward:
                        av,sv = frob(div(b,a),-t),s-t
                    else:
                        av,sv = div(b,frob(a,t)),s+t
                    expressions[v] = (av,sv%m,-sign)
                    stack.append(v)

        minus,plus = [],[]
        subgroup = order
        for j in extras:
            u,v,t,b = edges[j]
            a,s,e = expressions[u]
            av,sv,f = expressions[v]
            k = (sv+t-s)%m
            d = frob(div(b,field.mul(a,frob(av,t))),-s)
            d = d if f==1 else field.inverse(d)
            if e==f:
                plus.append((k,d))
                subgroup = gcd(subgroup,(1<<k)+1)
            else:
                minus.append((k,d))
                subgroup = gcd(subgroup,(1<<k)-1)

        # Each linear constraint is F^s(T)=c F^r(T).
        linear = [(k,d,0) for k,d in minus]
        if plus:
            r,c = plus[0]
            linear.extend((k,div(d,c),r) for k,d in plus[1:])
            linear.append((2*r,div(frob(c,r),c),0))
        rows = []
        for s,d,r0 in linear:
            cols = [frob(1<<i,s)^field.mul(d,frob(1<<i,r0)) for i in range(m)]
            for j in range(m):
                rows.append((sum(((v>>j)&1)<<i for i,v in enumerate(cols)),0))
        _,basis,_ = affine_domain(m,rows)
        if not basis:
            return None
        point = basis[0]
        if plus:
            r,c = plus[0]
            correction = frob(div(c,field.mul(point,frob(point,r))),-1)
            point = field.mul(point,correction)
        if any(frob(point,k)!=field.mul(d,point) for k,d in minus):
            return None
        if any(field.mul(point,frob(point,k))!=d for k,d in plus):
            return None
        exps = []
        for v in vertices:
            a,s,e = expressions[v]
            factor = frob(point,s)
            answer[v] = field.mul(a,factor if e==1 else field.inverse(factor))
            exps.append(e*(1<<s))
        components.append(Component(tuple(vertices),tuple(exps),subgroup))

    if any(field.mul(answer[u],frob(answer[v],t))!=b for u,v,t,b in edges):
        raise ArithmeticError("invalid lifted product witness")
    return Basepoint(tuple(answer),tuple(components))

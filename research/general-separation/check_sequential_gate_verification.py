"""Bounded exact integer-arithmetic controls for sequential gate certificates."""
from itertools import product


def value(table,a,b):
    return (table >> (2*a+b)) & 1


def real_residual(table,H,A,B,C):
    """A,B,C are numerators; the already certified parents must be bivalent."""
    assert H > 0 and len(A) == len(B) == len(C)
    f00,f01,f10,f11 = [value(table,a,b) for a,b in product((0,1),repeat=2)]
    total = 0
    for u,v,w in zip(A,B,C):
        assert u in (0,H) and v in (0,H)
        # H^2 times the multilinear two-input gate polynomial.
        P = H*H*f00 + H*u*(f10-f00) + H*v*(f01-f00) + u*v*(f11-f10-f01+f00)
        expanded = H*w*w - 2*w*P + H*P
        direct = H*(w-H*value(table,u//H,v//H))**2
        assert expanded == direct >= 0
        total += expanded
    return total


def integer_nand(A,B,C):
    assert all(type(c) is int for c in C)
    assert all(v in (0,1) for v in (*A,*B))
    if sum(c*(c-1) for c in C) != 0:
        return False
    D = [1-c for c in C]
    outside_a = sum(d*(1-a) for d,a in zip(D,A))
    outside_b = sum(d*(1-b) for d,b in zip(D,B))
    size = sum(a*b for a,b in zip(A,B))
    return outside_a == outside_b == 0 and sum(D) == size


def layers():
    for H in (1,2,5):
        A = [0,0,H,H]
        B = [0,H,0,H]
        wires = [A,B,[H]*4,[0]*4]
        for gate in range(16):
            for u,v in ((A,B),(B,A),(A,A),(wires[-1],A)):
                target = [H*value(gate,a//H,b//H) for a,b in zip(u,v)]
                assert real_residual(gate,H,u,v,target) == 0
                for j in range(4):
                    bad = target.copy()
                    bad[j] += 1
                    assert real_residual(gate,H,u,v,bad) == H
            wires.append(target)


def inclusions():
    for A in product((0,1),repeat=3):
        for B in product((0,1),repeat=3):
            for C in product((-1,0,1,2),repeat=3):
                target = tuple(1-a*b for a,b in zip(A,B))
                assert integer_nand(A,B,C) == (C == target)
    # Proper subset meets both inclusions; equal-cardinality wrong supports
    # meet one of the inclusions each. All three conditions are needed.
    A,B = (1,1,0),(1,0,1)
    for D,expected in [((0,0,0),(0,0,False)),((0,1,0),(0,1,True)),
                       ((0,0,1),(1,0,True))]:
        assert (sum(d*(1-a) for d,a in zip(D,A)),
                sum(d*(1-b) for d,b in zip(D,B)),
                sum(D)==sum(a*b for a,b in zip(A,B))) == expected


def reflection():
    H = 2
    A,B = (0,0,1,1),(0,1,0,1)
    correct = [2*a*b for a,b in zip(A,B)]
    reflected = [2*a+2*b-1-2*a*b for a,b in zip(A,B)]
    for direction in ((1,1,1,1),A,B):
        assert sum(q*x for q,x in zip(correct,direction)) == sum(
            q*x for q,x in zip(reflected,direction))
    assert sum(q*q for q in correct) == sum(q*q for q in reflected)
    assert correct != reflected and sum(q*(q-H) for q in reflected) == 0
    assert real_residual(8,H,[2*a for a in A],[2*b for b in B],reflected) == 8


if __name__ == '__main__':
    layers()
    inclusions()
    reflection()
    print('Sequential real and integer gate checks and reflected-parent moments agree.')

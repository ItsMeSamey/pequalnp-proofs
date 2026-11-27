import itertools
import math
import random
import time
from cover import *


def family(n):
    t = math.isqrt(n)
    raw = lambda j: 1 << (1 + j % n)
    gate = lambda j: 1 << (1 + n + j)
    gates = [(raw(2*j), raw(2*j+1), 0) for j in range(t)]
    while len(gates) < n * (n-1).bit_length():
        i = len(gates)
        gates.append(((gate(i-1) if i > t else 0) ^ raw(i),
                      gate((i-t) % t) ^ raw(i+2), raw(i+3)))
    return gates, gate(len(gates)-1)


def exhaustive_backend(system, pins, assignment):
    bits = [b for b, _ in system.definitions]
    count = 0
    for x in range(1 << system.n):
        if x & pins != assignment:
            continue
        for values in itertools.product(range(2), repeat=len(bits)):
            word = 1 | x << 1 | sum(b*v for b,v in zip(bits,values))
            if all(value(poly, word) == int(bool(b & word)) for b,poly in system.definitions):
                count += value(system.final, word)
    return count


def run():
    rng = random.Random(551)
    for case in range(150):
        n, m = rng.randrange(1, 5), rng.randrange(1, 7)
        gates = [tuple(rng.randrange(1 << (n+i+1)) for _ in range(3)) for i in range(m)]
        out = rng.randrange(1 << (n+m+1))
        edges = conflicts(n, gates, out)
        for mask in range(1 << m):
            S = {i for i in range(m) if mask >> i & 1}
            try:
                sys = compile_system(n, gates, out, S)
            except ValueError:
                assert any(S.isdisjoint(edge) for edge in edges)
                continue
            assert all(S.intersection(edge) for edge in edges)
            assert all(sys.evaluate(x) == direct(n,gates,out,x) for x in range(1<<n))
            if case < 20 and len(S) <= 2:
                assert sys.count_witness(exhaustive_backend)[0] == sys.count_witness()[0]
    for n in (8,16,32):
        gates,out = family(n)
        edges = conflicts(n,gates,out)
        nodes = {}
        S = search_cover(edges,math.isqrt(n),nodes)
        assert S is not None and not search_cover(edges,0)
        system = compile_system(n,gates,out,S)
        inputs = range(1<<n) if n<=8 else [rng.randrange(1<<n) for _ in range(256)]
        start=time.perf_counter()
        truth=[direct(n,gates,out,x) for x in inputs]
        d=time.perf_counter()-start
        start=time.perf_counter()
        assert truth==[system.evaluate(x) for x in inputs]
        print(n,len(gates),len(S),nodes,len(inputs),sum(truth),round(d,4),round(time.perf_counter()-start,4))


if __name__ == '__main__':
    run()

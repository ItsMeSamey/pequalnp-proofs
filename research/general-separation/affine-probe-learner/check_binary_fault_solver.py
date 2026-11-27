"""Original assignment controls; execution delegated to the organizer."""
from itertools import combinations, product


class Source:
    def __init__(self,n):
        self.n = n
        self.gates = []

    def nand(self,u,v):
        wire = self.n+len(self.gates)
        self.gates.append((u,v))
        return wire

    def inv(self,u):
        return self.nand(u,u)

    def both(self,u,v):
        return self.inv(self.nand(u,v))

    def xor(self,u,v):
        m = self.nand(u,v)
        return self.nand(self.nand(u,m),self.nand(v,m))

    def finish(self,out):
        return tuple(self.gates),out


def raw(n,F,x):
    values = {-1:0,-2:1,**{i:(x >> (n-i-1)) & 1 for i in range(n)}}
    for w,(i,j) in enumerate(F[0],n):
        values[w] = int(not (values[i] and values[j]))
    return values[F[1]]


COLUMNS = (1,2,4,3,5,6,7)


def simplex():
    circuit = Source(7)
    out = -2
    for i,mask in enumerate(COLUMNS[3:],3):
        target = -2
        for basis in range(3):
            if mask & (1 << basis):
                target = circuit.xor(target,basis)
        out = circuit.both(out,circuit.inv(circuit.xor(target,i)))
    return circuit.finish(out)


def codewords():
    return {sum((((mask&s).bit_count()%2) ^ (i>=3)) << (6-i)
                for i,mask in enumerate(COLUMNS)) for s in range(8)}


def fixtures(n):
    c = Source(n)
    out = 0
    for i in range(1,n):
        out = c.both(out,i)
    positive = c.finish(out)
    c = Source(n)
    return positive,c.finish(c.both(0,c.inv(0)))


def warm():
    from binary_fault_retraction import Gamma,compile_retraction
    gamma = Gamma(3)
    cubes = (((0,1),(1,0)),((1,1),(2,0)))
    for cube in cubes:
        assert gamma.add_cube(cube)
        assert not gamma.add_cube(cube)
    true_gamma = {x for x in range(8) if all(
        any((x >> (2-i)) & 1 != b for i,b in cube) for cube in cubes)}
    assert true_gamma == {0,1,3,7}
    assert {x for x in range(8) if gamma.accepts(x)} == true_gamma
    assert gamma.model() in true_gamma
    src = fixtures(3)[0]
    for anchor in sorted(true_gamma):
        retracted = compile_retraction(3,*src,gamma,anchor)
        for x in range(8):
            old = retracted.lift(x)
            assert old in true_gamma
            assert old == (x if x in true_gamma else anchor)
            if x in true_gamma:
                assert x == old
            assert raw(retracted.n,(retracted.gates,retracted.output),x) == raw(3,src,old)
    inconsistent = Gamma(1)
    for b in (0,1):
        inconsistent.add_cube(((0,b),))
    assert inconsistent.model() is None
    try:
        compile_retraction(1,(),0,inconsistent)
    except ValueError:
        pass
    else:
        raise AssertionError('inconsistent Gamma accepted')


def respects(n,clauses,x):
    return all(any(((x >> (n-i-1)) & 1) == b for i,b in clause)
               for clause in clauses)


def small_sources():
    from binary_fault_solver import solve
    for F,positive in ((((),-1),False),(((),-2),True)):
        got = solve(0,F)
        assert (got['status'] == 'witness') == positive
        if positive:
            assert got['assignment'] == 0
    n = 4
    for F in fixtures(n):
        accepted = [x for x in range(1 << n) if raw(n,F,x)]
        got = solve(n,F)
        assert all(respects(n,got['clauses'],x) for x in accepted)
        assert got['fresh_clauses'] == len(set(got['clauses']))
        if accepted:
            assert accepted == [15] and got['assignment'] == 15
            assert got['status'] == 'witness' and got['k'] == 0
            assert got['false_crossings'] <= n and got['crossings'] < 15
        else:
            assert got['status'] == 'unsat'
            assert got['fresh_clauses'] == 2 and got['k'] == 0
            assert set(got['clauses']) == {((0,0),),((0,1),)}
            assert got['phases'] == got['crossings'] == got['false_crossings'] == 2
            assert got['reason'] == '2sat'


def code_control():
    from binary_fault_retraction import exclusion_cube
    n,F = 7,simplex()
    words = {x for x in range(128) if raw(n,F,x)}
    assert words == codewords() and min(words) == 15
    for i,j in combinations(range(n),2):
        assert {((x>>i)&1,(x>>j)&1) for x in words} == set(product((0,1),repeat=2))
    def traversal(lo,hi):
        if lo <= hi:
            mid = (lo+hi)//2
            yield mid
            yield from traversal(lo,mid-1)
            yield from traversal(mid+1,hi)
    tested = []
    for x in traversal(1,127):
        tested.append(x)
        if x in words:
            break
        assert exclusion_cube(n,*F,x) is None
    assert tested[:3] == [64,32,16] and tested[-1] == 15 and len(tested) == 18

    # Reconstruct each public endpoint once. The global solver walks the
    # unmodified original code because no fresh binary clause can be sound.
    from binary_fault_solver import solve
    from primitive_rewrite_chain import endpoint
    def finite_factory(width,source):
        assert width == n and source == F
        indices = {endpoint(n,*F,j):j for j in range(-1,128)}
        assert len(indices) == 129
        pool = [(u,b) for u in range(128) for b in (0,1) if (u,b) != (0,1)]
        def predict(h,cap,history,query):
            restrictions = [(indices[q],answer) for q,answer in history]
            cut = indices[query]
            candidates = [(u,b) for u,b in pool if all(
                (b and u <= t) == answer for t,answer in restrictions)]
            return int(2*sum(b and u <= cut for u,b in candidates) > len(candidates))
        return predict
    got = solve(n,F,learner_factory=finite_factory,bound=n)
    assert got['fresh_clauses'] == 0 and got['phases'] == 1
    assert got['assignment'] == 15 and got['false_crossings'] == 17 and got['crossings'] == 18


if __name__ == '__main__':
    warm()
    small_sources()
    code_control()
    print('Warm binary projection, tiny solver and 7-coordinate code controls passed.')

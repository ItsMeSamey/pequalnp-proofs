"""Kleene exclusions, binary-clause learning, and explicit NAND retractions.

Input 0 is the most significant bit. Constants -1 and -2 mean zero and one.
A literal (i,b) is true when the value of input i is b.
"""
from dataclasses import dataclass
from itertools import combinations

from primitive_rewrite_chain import _inputs


def _assignment(n, x):
    if type(x) is not int or not 0 <= x < 1 << n:
        raise ValueError('assignment out of range')


def _value(n, x, i):
    return (x >> (n-i-1)) & 1


def exclusion_cube(n, gates, output, x):
    """First certified zero cube containing x, in width/coordinate order.

    An empty tuple certifies a global zero. None means no tested cube certified
    zero, including when F(x)=1. Unknown NAND inputs use strong Kleene logic.
    """
    gates = _inputs(n, gates, output)
    _assignment(n, x)
    bits = tuple(_value(n, x, i) for i in range(n))

    def forced_zero(cube):
        values = [None] * n
        for i, bit in cube:
            values[i] = bit
        for a, b in gates:
            u = values[a] if a >= 0 else -1-a
            v = values[b] if b >= 0 else -1-b
            if u == 0 or v == 0:
                values.append(1)
            elif u == v == 1:
                values.append(0)
            else:
                values.append(None)
        result = values[output] if output >= 0 else -1-output
        return result == 0

    for size in range(min(2, n) + 1):
        for indices in combinations(range(n), size):
            cube = tuple((i, bits[i]) for i in indices)
            if forced_zero(cube):
                return cube
    return None


def _accepts(n, clauses, x):
    _assignment(n, x)
    return all(any(_value(n, x, i) == bit for i, bit in clause) for clause in clauses)


def _finish_order(edges):
    seen = set()
    order = []
    for start in range(len(edges)):
        if start in seen:
            continue
        seen.add(start)
        stack = [(start, iter(edges[start]))]
        while stack:
            vertex, children = stack[-1]
            child = next(children, None)
            if child is None:
                order.append(vertex)
                stack.pop()
            elif child not in seen:
                seen.add(child)
                stack.append((child, iter(edges[child])))
    return order


class Gamma:
    """Conjunction of complements of width-at-most-two exclusion cubes."""
    def __init__(self, n):
        if type(n) is not int or n < 0:
            raise ValueError('invalid input width')
        self.n = n
        self._clauses = {}

    @property
    def clauses(self):
        return tuple(self._clauses)

    def add_cube(self, cube):
        pins = {}
        for i, bit in cube:
            if type(i) is not int or not 0 <= i < self.n or type(bit) is not int or bit not in (0, 1):
                raise ValueError('invalid cube literal')
            if i in pins and pins[i] != bit:
                raise ValueError('contradictory cube')
            pins[i] = bit
            if len(pins) > 2:
                raise ValueError('cube exceeds width two')
        clause = tuple((i, 1 ^ pins[i]) for i in sorted(pins))
        fresh = clause not in self._clauses
        self._clauses[clause] = None
        return fresh

    def accepts(self, x):
        return _accepts(self.n, self._clauses, x)

    def model(self):
        """Kosaraju components, in source-to-sink order on the implication DAG."""
        if () in self._clauses:
            return None
        graph = [[] for _ in range(2*self.n)]
        reverse = [[] for _ in graph]
        for clause in self._clauses:
            a = 2*clause[0][0] + clause[0][1]
            b = 2*clause[-1][0] + clause[-1][1]
            for u, v in ((a ^ 1, b), (b ^ 1, a)):
                graph[u].append(v)
                reverse[v].append(u)
        component = [-1] * len(graph)
        for label, start in enumerate(reversed(_finish_order(graph))):
            if component[start] >= 0:
                continue
            component[start] = label
            stack = [start]
            while stack:
                for v in reverse[stack.pop()]:
                    if component[v] < 0:
                        component[v] = label
                        stack.append(v)
        result = 0
        for i in range(self.n):
            a, b = component[2*i:2*i+2]
            if a == b:
                return None
            result = (result << 1) | int(b > a)
        return result


@dataclass(frozen=True)
class Retracted:
    n: int
    gates: tuple
    output: int
    clauses: tuple
    anchor: int

    def lift(self, x):
        return x if _accepts(self.n, self.clauses, x) else self.anchor


def compile_retraction(n, gates, output, gamma, anchor=None):
    """Compile F(R(u)) and freeze the map back to original coordinates.

    For m clauses and s source gates this uses at most s+3n+3m NAND gates.
    Gamma must have a satisfying anchor.
    """
    gates = _inputs(n, gates, output)
    if not isinstance(gamma, Gamma) or gamma.n != n:
        raise ValueError('incompatible Gamma')
    clauses = gamma.clauses
    if anchor is None:
        anchor = gamma.model()
    if anchor is None or not _accepts(n, clauses, anchor):
        raise ValueError('a satisfying anchor is required')
    if not clauses:
        return Retracted(n, gates, output, clauses, anchor)

    compiled = []

    def nand(a, b):
        compiled.append((a, b))
        return n + len(compiled) - 1

    neg = {}

    def complement(i):
        if i not in neg:
            neg[i] = nand(i, i)
        return neg[i]

    def literal(i, bit):
        return i if bit else complement(i)

    conjunction = -2
    for clause in clauses:
        if len(clause) == 1:
            clause_wire = literal(*clause[0])
        else:
            (i, a), (j, b) = clause
            clause_wire = nand(literal(i, 1 ^ a), literal(j, 1 ^ b))
        if conjunction == -2:
            conjunction = clause_wire
        else:
            inverse = nand(conjunction, clause_wire)
            conjunction = nand(inverse, inverse)

    wires = {-1: -1, -2: -2}
    for i in range(n):
        if _value(n, anchor, i):
            wires[i] = nand(conjunction, complement(i))
        else:
            inverse = nand(conjunction, i)
            wires[i] = nand(inverse, inverse)
    for i, (a, b) in enumerate(gates, n):
        wires[i] = nand(wires[a], wires[b])
    return Retracted(n, tuple(compiled), wires[output], clauses, anchor)

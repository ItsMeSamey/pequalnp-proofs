"""Primitive shared-DAG proofs of Q(j)=Q(j-1) at a false assignment.

Input zero is the most significant bit, gate i has address n+i,
and -1 and -2 are Boolean constants zero and one.
"""
from dataclasses import dataclass


@dataclass(frozen=True)
class Step:
    context: int
    left: int
    right: int
    rule: str


@dataclass(frozen=True)
class Chain:
    nodes: tuple
    roots: tuple
    steps: tuple


_OPS = {'not', 'and', 'or', 'nand'}


def _order(nodes, root):
    """Reachable postorder, visiting the left operand first."""
    done = set()
    stack = [(root, False)]
    while stack:
        wire, exiting = stack.pop()
        if wire in done:
            continue
        if exiting:
            done.add(wire)
            yield wire
            continue
        stack.append((wire, True))
        key = nodes[wire]
        if key[0] in _OPS:
            stack.extend((v, False) for v in reversed(key[1:]))


class _Terms:
    def __init__(self):
        self.ids = {}
        self.nodes = []
        self.open = []
        self.zero = self.make('const', 0)
        self.one = self.make('const', 1)
        self.hole = self.make('hole')

    def make(self, op, *args):
        key = (op, *args)
        if key not in self.ids:
            self.ids[key] = len(self.nodes)
            self.nodes.append(key)
            self.open.append(op == 'hole' or (op in _OPS and any(self.open[i] for i in args)))
        return self.ids[key]

    def plug(self, context, side):
        mapped = {self.hole: side}
        stack = [(context, False)]
        while stack:
            node, exiting = stack.pop()
            if node in mapped:
                continue
            if not self.open[node]:
                mapped[node] = node
                continue
            op, *args = self.nodes[node]
            if exiting:
                mapped[node] = self.make(op, *(mapped[i] for i in args))
            else:
                stack.append((node, True))
                stack.extend((i, False) for i in args)
        return mapped[context]


def _inputs(n, gates, output):
    if type(n) is not int or n < 0:
        raise ValueError('n must be nonnegative')
    if type(gates) not in (tuple, list) or any(type(pair) not in (tuple, list) for pair in gates):
        raise ValueError("gates must be an ordered list of NAND pairs")
    gates = tuple(tuple(pair) for pair in gates)
    for i, pair in enumerate(gates):
        if len(pair) != 2 or any(type(w) is not int or not -2 <= w < n+i for w in pair):
            raise ValueError('invalid NAND predecessor')
    if type(output) is not int or not -2 <= output < n + len(gates):
        raise ValueError('invalid output wire')
    return gates


def evaluate(n, gates, output, x):
    gates = _inputs(n, gates, output)
    if type(x) is not int or not 0 <= x < 1 << n:
        raise ValueError('assignment out of range')
    values = {-1: 0, -2: 1}
    values.update((i, (x >> (n-1-i)) & 1) for i in range(n))
    for i, (a, b) in enumerate(gates, n):
        values[i] = 1 ^ (values[a] & values[b])
    return values[output]


def _source(t, n, gates):
    wires = {-1: t.zero, -2: t.one}
    wires.update((i, t.make('var', i)) for i in range(n))
    for i, (a, b) in enumerate(gates, n):
        wires[i] = t.make('nand', wires[a], wires[b])
    return wires


def _path(t, n, j):
    """Path conjunctions, path literals, and OR of cubes strictly before j."""
    prefixes, literals, acc = [t.one], [], t.zero
    for i in range(n):
        x = t.make('var', i)
        bit = (j >> (n-1-i)) & 1
        if bit:
            sibling = t.make('and', prefixes[-1], t.make('not', x))
            acc = t.make('or', acc, sibling)
        lit = x if bit else t.make('not', x)
        literals.append(lit)
        prefixes.append(t.make('and', prefixes[-1], lit))
    return prefixes, literals, acc


def _endpoint(t, n, source, j):
    if j == -1:
        return t.zero
    if j == (1 << n) - 1:
        return source
    return t.make('and', source, _path(t, n, j+1)[2])


def normalize(n, nodes, root):
    """Compile ordered expressions, hash-cons NANDs, then renumber by postorder."""
    target = _Terms()
    make = target.make
    compiled = {}
    for i in _order(nodes, root):
        op, *args = nodes[i]
        if op in ('const', 'var'):
            wire = make(op, *args)
        elif op in _OPS:
            a = compiled[args[0]]
            if op == 'not':
                wire = make('nand', a, a)
            else:
                b = compiled[args[1]]
                if op == 'or':
                    wire = make('nand', make('nand', a, a), make('nand', b, b))
                else:
                    wire = make('nand', a, b)
                    if op == 'and':
                        wire = make('nand', wire, wire)
        else:
            raise ValueError('cannot present a hole')
        compiled[i] = wire
    root = compiled[root]
    gates, addresses = [], {}
    for i in _order(target.nodes, root):
        op, *args = target.nodes[i]
        if op == 'const':
            addresses[i] = -1-args[0]
        elif op == 'var':
            addresses[i] = args[0]
        else:
            addresses[i] = n + len(gates)
            gates.append(tuple(addresses[a] for a in args))
    return tuple(gates), addresses[root]


def endpoint(n, gates, output, j):
    gates = _inputs(n, gates, output)
    if type(j) is not int or not -1 <= j < 1 << n:
        raise ValueError('prefix index out of range')
    t = _Terms()
    source = _source(t, n, gates)[output]
    return normalize(n, t.nodes, _endpoint(t, n, source, j))


def public_cap(n, s):
    if any(type(v) is not int or v < 0 for v in (n, s)):
        raise ValueError('negative dimension or gate count')
    # Raw and shielded source gates, prefix paths, and the working conjunction
    # fit this allowance even when each Boolean macro emits three NANDs.
    return 256 * (s + n*n + 1)


def build_chain(n, gates, output, j):
    gates = _inputs(n, gates, output)
    if evaluate(n, gates, output, j):
        raise ValueError('point is not a zero of the circuit')
    t = _Terms()
    make, hole = t.make, t.hole
    zero, one = t.zero, t.one
    wires = _source(t, n, gates)
    source = wires[output]
    prefixes, lits, old = _path(t, n, j)
    guard = prefixes[-1]
    roots = [_endpoint(t, n, source, j)]
    steps = []

    def emit(context, left, right, rule):
        if left == right:
            return
        if t.plug(context, left) != roots[-1]:
            raise AssertionError('rewrite context does not produce current root')
        roots.append(t.plug(context, right))
        steps.append(Step(context, left, right, rule))

    def A(a, b):
        return make('and', a, b)

    def O(a, b):
        return make('or', a, b)

    def N(a, b):
        return make('nand', a, b)

    # Build the increment in its natural direction and replay it backward.
    carry = []
    acc, cube = old, guard
    i = n-1
    while i >= 0 and (j >> (n-1-i)) & 1:
        _, earlier, sibling = t.nodes[acc]
        carry.append((hole, O(acc, cube), O(earlier, O(sibling, cube)), 'or_assoc'))
        carry.append((O(earlier, hole), O(sibling, cube), prefixes[i], 'sibling'))
        acc, cube = earlier, prefixes[i]
        i -= 1
    if j == (1 << n)-1:
        carry.append((hole, O(zero, one), one, 'zero_or'))
        emit(hole, source, A(source, one), 'and_one')
    for ctx, lhs, rhs, rule in reversed(carry):
        emit(A(source, ctx), rhs, lhs, rule)
    left = A(source, old)
    emit(hole, A(source, O(old, guard)), O(left, A(source, guard)), 'distribute')
    emit(O(left, hole), A(source, guard), A(guard, source), 'and_commute')

    reachable = {output}
    for w in range(n+len(gates)-1, n-1, -1):
        if w in reachable:
            reachable.update(gates[w-n])
    order = sorted(reachable)
    expanded = set()
    reduced = {}

    def slot_context(slot):
        # Rebuild the guarded branch by original wire identity. All intended
        # uses share one placeholder; the other copy of the source stays raw.
        rendered = {}
        for w in order:
            if w == slot:
                rendered[w] = hole
            elif w in reduced:
                rendered[w] = reduced[w]
            elif w in expanded:
                a, b = gates[w-n]
                rendered[w] = A(guard, N(rendered[a], rendered[b]))
            else:
                rendered[w] = A(guard, wires[w])
        return O(left, rendered[output])

    for w in reversed(order):
        if w < n:
            continue
        a, b = gates[w-n]
        emit(slot_context(w), A(guard, wires[w]),
             A(guard, N(A(guard, wires[a]), A(guard, wires[b]))), 'shield')
        expanded.add(w)

    for w in order:
        if w >= n:
            break
        context = slot_context(w)
        if w < 0:
            result = guard if w == -2 else zero
            emit(context, A(guard, wires[w]), result, 'and_one' if w == -2 else 'and_zero')
            reduced[w] = result
            continue
        x = wires[w]
        suffix = []

        def at_focus():
            work = hole
            for lit in reversed(suffix):
                work = A(work, lit)
            return t.plug(context, work)

        for i in range(n-1, w, -1):
            parent, lit = prefixes[i], lits[i]
            emit(at_focus(), A(A(parent, lit), x), A(A(parent, x), lit), 'and_swap_tail')
            suffix.append(lit)
        parent, lit = prefixes[w], lits[w]
        focus = at_focus()
        emit(focus, A(A(parent, lit), x), A(parent, A(lit, x)), 'and_assoc')
        positive = lit == x
        emit(t.plug(focus, A(parent, hole)), A(lit, x), x if positive else zero,
             'and_idem' if positive else 'neg_and')
        if not positive:
            emit(focus, A(parent, zero), zero, 'and_zero')
            while suffix:
                outer = suffix.pop()
                emit(at_focus(), A(zero, outer), zero, 'zero_and')
        reduced[w] = guard if positive else zero

    for w in order:
        if w < n:
            continue
        a, b = gates[w-n]
        av, bv = reduced[a], reduced[b]
        aa, bb = ('0' if av == zero else 'm'), ('0' if bv == zero else 'm')
        result = zero if aa == bb == 'm' else guard
        emit(slot_context(w), A(guard, N(av, bv)), result, 'nand_'+aa+bb)
        reduced[w] = result
    if reduced[output] != zero:
        raise AssertionError('guarded output did not reduce to zero')
    emit(hole, O(left, zero), left, 'or_zero')
    if j == 0:
        emit(hole, left, zero, 'and_zero')
    if roots[-1] != _endpoint(t, n, source, j-1):
        raise AssertionError('unexpected lower endpoint')
    return Chain(tuple(t.nodes), tuple(roots), tuple(steps))

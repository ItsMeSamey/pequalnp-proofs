"""Unseeded paired boundary DP with circuit and homogeneous block solvers."""
from pathlib import Path
import sys

sys.path.append(str(Path(__file__).resolve().parents[1] / "unseeded-root-states"))
from pairs import project_value, restrictions
from solve import augment, canonical, eliminate, functional, image, intersection, solve
from three import three_witness


def same_component(local, a, b):
    """Connectivity of the two named elements in the binary column matroid."""
    columns = [v for _, v in local] + [a, b]
    _, fundamental_circuits = eliminate(columns)
    parents = list(range(len(columns)))

    def root(i):
        while parents[i] != i:
            parents[i] = parents[parents[i]]
            i = parents[i]
        return i

    for circuit in fundamental_circuits:
        lowest = circuit & -circuit
        i = lowest.bit_length() - 1
        rest = circuit ^ lowest
        while rest:
            bit = rest & -rest
            parents[root(bit.bit_length() - 1)] = root(i)
            rest ^= bit
    return root(len(columns) - 2) == root(len(columns) - 1)


def circuit_witness(local, a, b):
    """Return ordinary support of a common circuit through a,b, if one exists."""
    if not same_component(local, a, b):
        return None
    kept = list(local)
    for item in local:
        trial = [other for other in kept if other[0] != item[0]]
        if same_component(trial, a, b):
            kept = trial
    return sum(1 << i for i, _ in kept)


def small_port(local, port, triple=None, homogeneous=None):
    width = len(port)
    if (width > 3 or (width == 3 and triple is None)) and homogeneous is None:
        raise ValueError("this port needs a triple-circuit or homogeneous witness oracle")
    cols = tuple(v for _, v in local)
    table = {f: {0: 0} for f in range(1 << width)}
    for coords in range(1, 1 << width):
        u = image(port, coords)
        support = solve(cols, u)
        assert support is not None
        table[0][u] = sum(1 << idx for j,(idx,_) in enumerate(local) if support >> j & 1)
        if width == 2:
            # The unique nonzero covector killing u has kernel exactly its line.
            f = next(f for f in range(1, 4) if not (f & coords).bit_count() % 2)
            a = next(v for v in port if v != u)
            witness = circuit_witness(local, a, a ^ u)
            if witness is not None:
                table[f][u] = witness
        if width == 3 and triple is not None:
            for f in range(1, 8):
                if not (f & coords).bit_count() % 2:
                    witness = three_witness(local, port, coords, f, triple)
                    if witness is not None:
                        table[f][u] = witness
        if width > 3 or (width == 3 and triple is None):
            from regular_state import solve_regular_state
            for f in range(1, 1 << width):
                if (f & coords).bit_count() % 2:
                    continue
                witness = solve_regular_state(local, port, coords, f, homogeneous)
                if witness == "unsupported":
                    raise ValueError("both homogeneous projections are unsupported for this state")
                if witness is not None:
                    table[f][u] = witness
    return table


def state_table(ordinary, roots, blocks, layout, triple=None, homogeneous=None, graphics=None):
    """Outer tree leaves are block indices. Stored supports use original indices."""
    def prepare(node):
        if isinstance(node, int):
            if not 0 <= node < len(blocks):
                raise ValueError("invalid block index")
            return tuple(blocks[node]), (node,), None
        if not isinstance(node, tuple) or len(node) != 2:
            raise ValueError("use block indices and ordered pairs for the tree")
        left, right = map(prepare, node)
        return left[0] + right[0], left[1] + right[1], (left, right)

    top = prepare(layout)
    if sorted(top[0]) != list(range(len(ordinary))) or sorted(top[1]) != list(range(len(blocks))):
        raise ValueError("outer layout must partition all columns into its distinct blocks")
    peak_width = 0

    def visit(node, outside):
        nonlocal peak_width
        ids, _, children = node
        port = intersection(canonical(ordinary[i] for i in ids), outside)
        peak_width = max(peak_width, len(port))
        if children is None:
            if graphics is not None and node[1][0] in graphics:
                local = [(i, ordinary[i]) for i in ids]
                return port, graphics[node[1][0]].table(local, port)
            return port, small_port([(i, ordinary[i]) for i in ids], port, triple, homogeneous)
        left, right = children
        left_port, left_table = visit(left, canonical(outside + tuple(ordinary[i] for i in right[0])))
        right_port, right_table = visit(right, canonical(outside + tuple(ordinary[i] for i in left[0])))
        union = canonical(left_port + right_port)
        lmap, rmap, pmap = (restrictions(union, p) for p in (left_port, right_port, port))
        wanted = {image(port, mask) for mask in range(1 << len(port))}
        table = {}
        for f in range(1 << len(union)):
            result = table.setdefault(project_value(f, pmap), {})
            for u, first in left_table[project_value(f, lmap)].items():
                for v, second in right_table[project_value(f, rmap)].items():
                    if u ^ v in wanted:
                        result.setdefault(u ^ v, first | second)
        return port, table

    port, table = visit(top, canonical(roots))
    return port, table, peak_width


def spectrum(base, primal, dual, t, blocks, layout, triple=None, homogeneous=None, graphics=None):
    """Return each feasible score with an original cycle/cocycle, plus outer width."""
    ordinary, roots = augment(base, primal, dual, t)
    port, table, width = state_table(ordinary, roots, blocks, layout, triple, homogeneous, graphics)
    found = {}
    for b in range(1 << t):
        root_values = b << t
        alpha = functional(roots, root_values)
        if alpha is None:
            continue
        states = table[project_value(alpha, port)]
        for a in range(1 << t):
            v = image(roots, a)
            if v not in states or a ^ b in found:
                continue
            c = states[v]
            chosen = tuple(x for i, x in enumerate(ordinary) if c >> i & 1)
            phi = functional(roots + chosen, root_values)
            assert phi is not None
            d = sum(((phi & o).bit_count() % 2) << i for i, o in enumerate(ordinary))
            assert not c & d and not image(base, c)
            assert image(primal, c) == a and image(dual, d) == b
            found[a ^ b] = c, d
    return found, width

"""Exact DAG counts by independent linear projections, with capped parity splits."""
from fractions import Fraction
from affine_weight_portfolio import _affine


def basis(words):
    pivots = {}
    for word in words:
        while word:
            i = word.bit_length() - 1
            if i not in pivots:
                pivots[i] = word
                break
            word ^= pivots[i]
    return tuple(pivots[i] for i in sorted(pivots, reverse=True))


def common_direction(left, right):
    pivots = {word.bit_length() - 1: (word, 0) for word in left}
    for original in right:
        word = tag = original
        while word:
            i = word.bit_length() - 1
            if i not in pivots:
                pivots[i] = word, tag
                break
            previous, origin = pivots[i]
            word ^= previous
            tag ^= origin
        if not word and tag:
            return tag
    return 0


def unary(table, values):
    return [table >> index & 1 for index in values]


def counted(q, gates, max_splits=2):
    """Return an exact count and structural metrics, or None on depth cap."""
    stats = dict(leaves=0, max_depth=0, gate_visits=0, noncoordinate_splits=0)
    def leaf(form):
        return (form, (form >> 1,) if form >> 1 else (),
                Fraction(1, 2) if form >> 1 else Fraction(form & 1), 0)
    def invert(state):
        form, space, p, blocked = state
        return (None if form is None else form ^ 1, space,
                None if p is None else 1 - p, blocked)
    def descend(forms, depth):
        nodes = [leaf(form) for form in forms]
        for table, a, b in gates:
            stats['gate_visits'] += 1
            x, y = nodes[a], nodes[b]
            form = _affine(table, x[0], y[0])
            if form is not None:
                nodes.append(leaf(form))
                continue
            x0, x1, x2, x3 = unary(table, range(4))
            if a == b:
                col, operand = [x0, x3], x
            elif x0 == x1 and x2 == x3:
                col, operand = [x0, x2], x
            elif x0 == x2 and x1 == x3:
                col, operand = [x0, x1], y
            elif x[0] in (0, 1):
                col, operand = unary(table, [2*x[0], 2*x[0]+1]), y
            elif y[0] in (0, 1):
                col, operand = unary(table, [y[0], 2+y[0]]), x
            else:
                col = None
            if col is not None:
                if col[0] == col[1]:
                    nodes.append(leaf(col[0]))
                else:
                    nodes.append(operand if col[0] == 0 else invert(operand))
                continue
            space = basis((*x[1], *y[1]))
            blocked = x[3] or y[3] or common_direction(x[1], y[1])
            if blocked:
                nodes.append((None, space, None, blocked))
                continue
            px, py = x[2], y[2]
            p = sum(((1-px, px)[i] * (1-py, py)[j])
                    for i in (0, 1) for j in (0, 1) if table >> (2*i+j) & 1)
            nodes.append(leaf(int(p)) if p in (0, 1) else (None, space, p, 0))
        _, _, p, cut = nodes[-1]
        if p is not None:
            value = p * (1 << (q-depth))
            assert value.denominator == 1
            stats['leaves'] += 1
            stats['max_depth'] = max(stats['max_depth'], depth)
            return int(value)
        if depth == max_splits:
            return None
        assert cut
        pivot = 1 << (cut.bit_length() - 1)
        stats['noncoordinate_splits'] += int(cut.bit_count() > 1)
        total = 0
        for outcome in (0, 1):
            restricted = [(f ^ ((cut << 1) | outcome)) if (f >> 1) & pivot else f
                          for f in forms]
            subtotal = descend(restricted, depth + 1)
            if subtotal is None:
                return None
            total += subtotal
        return total
    value = descend([1 << (i+1) for i in range(q)], 0)
    return None if value is None else dict(count=value, **stats)

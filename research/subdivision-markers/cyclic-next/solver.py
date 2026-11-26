"""Cyclic native guards solved on a given binary tree of variable clusters."""

def span(columns):
    """Enumerate the distinct possible responses in a binary column space."""
    values = {0}
    for column in columns:
        if column not in values:
            values |= {row ^ column for row in values}
    return values


def solve(guards, labels, tree):
    """Return {xor_label: witness}. Tree is a vertex index or a pair of trees.

    A guard literal (mask, constant) is true iff parity(mask & assignment) XOR constant.
    Each selected bit requires at least one true literal from its guard.
    """
    n = len(guards)
    if not n:
        return {0: 0}
    columns = [0] * n
    owned = []
    offsets = 0
    r = 0
    for guard in guards:
        start = r
        for mask, constant in guard:
            offsets |= constant << r
            for j in range(n):
                if mask >> j & 1:
                    columns[j] |= 1 << r
            r += 1
        owned.append((1 << r) - (1 << start))
    allrows = (1 << r) - 1

    def visit(node):
        if isinstance(node, int):
            v = node
            rows = owned[v]
            table = {}
            for inc in span(columns[j] & rows for j in range(n) if j != v):
                options = {}
                for bit in (0, 1):
                    effect = columns[v] * bit
                    if bit and not ((inc ^ offsets ^ effect) & rows):
                        continue
                    out = effect & (allrows ^ rows)
                    options[out, labels[v]*bit] = bit << v
                table[inc] = options
            return 1 << v, rows, table
        lv, lr, left = visit(node[0])
        rv, rr, right = visit(node[1])
        vertices = lv | rv
        rows = lr | rr
        outside = allrows ^ rows
        table = {}
        outs_left = {out for options in left.values() for out,_ in options}
        outs_right = {out for options in right.values() for out,_ in options}
        for inc in span(columns[j] & rows for j in range(n) if not vertices >> j & 1):
            options = {}
            for lo in outs_left:
                rinc = (inc ^ lo) & rr
                for ro in outs_right:
                    linc = (inc ^ ro) & lr
                    out = (lo ^ ro) & outside
                    for (p,a),x in left[linc].items():
                        if p != lo:
                            continue
                        for (q,b),y in right[rinc].items():
                            if q == ro:
                                options[out,a^b] = x | y
            table[inc] = options
        return vertices, rows, table
    _,_,table = visit(tree)
    return {marker: x for (out,marker),x in table[0].items()}

"""Modular linear support on an explicit common-order weighted program."""
def in_span(rows, target, precision):
    if type(precision) != int or precision < 1:
        raise ValueError("positive modulus precision required")
    modulus = 1 << precision
    pending = [[x % modulus for x in row] for row in rows]
    target = [x % modulus for x in target]
    while pending and target:
        best = None
        for i, row in enumerate(pending):
            if len(row) != len(target):
                raise ValueError("row width")
            for j, entry in enumerate(row):
                if entry:
                    choice = (entry & -entry, i, j)
                    if best is None or choice < best:
                        best = choice
        if best is None:
            break
        power, i, column = best
        if target[column] % power:
            return False
        pivot = pending.pop(i)
        inv = pow(pivot[column] // power, -1, modulus)
        pivot = [entry * inv % modulus for entry in pivot]
        def eliminate(row):
            multiplier = row[column] // power
            return [(x - multiplier*y) % modulus for j,(x,y) in enumerate(zip(row,pivot)) if j != column]
        target = eliminate(target)
        pending = [eliminate(row) for row in pending]
    return not any(target)


def nonzero(start, transitions, end, precision):
    """Return a prefix word as a tuple of bits, or None for the zero function."""
    if type(precision) != int or precision < 1:
        raise ValueError("positive modulus precision required")
    mod = 1 << precision
    prefixes = [(tuple(x % mod for x in start), ())]
    width = len(start)
    for choices in transitions:
        if len(choices) != 2 or any(len(matrix) != width for matrix in choices):
            raise ValueError("expected two transition matrices of current height")
        next_width = len(choices[0][0]) if width else 0
        if any(len(row) != next_width for matrix in choices for row in matrix):
            raise ValueError("inconsistent successor width")
        retained = []
        next_prefixes = []
        for row, prefix in prefixes:
            for bit, matrix in enumerate(choices):
                out = tuple(sum(x*matrix[i][j] for i,x in enumerate(row)) % mod for j in range(next_width))
                if not in_span(retained,out,precision):
                    retained.append(out)
                    next_prefixes.append((out,prefix+(bit,)))
        width = next_width
        prefixes = next_prefixes
    if len(end) != width:
        raise ValueError("terminal width")
    for row,prefix in prefixes:
        if sum(x*y for x,y in zip(row,end)) % mod:
            return prefix
    return None

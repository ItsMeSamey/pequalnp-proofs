"""Guard literals are (mask, constant); guards and labels follow topological order."""


def solve(guards, labels, target):
    """Return a witness bitmask or None for simultaneous affine terminal markers.

    labels[i] packs the marker coefficients of bit i. Constant terms are
    absorbed into target. Caller supplies the topological order.
    """
    n = len(guards)
    if len(labels) != n or target < 0 or any(label < 0 for label in labels):
        raise ValueError("invalid labels or target")
    future = [0] * (n + 1)
    count = 0
    occurrences = []
    columns = [0] * n
    for i, alternatives in enumerate(guards):
        row = []
        for mask, const in alternatives:
            if mask < 0 or mask.bit_length() > i or const not in (0, 1):
                raise ValueError("each guard must use only earlier bits")
            index = count
            count += 1
            row.append((index, const))
            future[i] |= 1 << index
            while mask:
                bit = mask & -mask
                columns[bit.bit_length()-1] |= 1 << index
                mask ^= bit
        occurrences.append(row)
    for i in reversed(range(n)):
        future[i] |= future[i + 1]

    # A representative assignment per partial signature.
    states = {(0, 0): 0}
    for i, row in enumerate(occurrences):
        next_states = {}
        for (responses, syndrome), witness in states.items():
            residual = responses & future[i + 1]
            next_states.setdefault((residual, syndrome), witness)
            if any(((responses >> j) & 1) ^ const for j, const in row):
                key = ((responses ^ columns[i]) & future[i + 1], syndrome ^ labels[i])
                next_states.setdefault(key, witness | (1 << i))
        states = next_states
    return states.get((0, target))


def unary_forest(parents, allowed, labels, target):
    """allowed[i][p] says whether bit i may equal one given parent bit p.

    Use parent -1 for roots, where p=0. Every vertex may always be zero.
    """
    n = len(parents)
    if len(allowed) != n or len(labels) != n:
        raise ValueError("inconsistent vertex arrays")
    children = [[] for _ in range(n)]
    roots = []
    for i, parent in enumerate(parents):
        if parent == -1:
            roots.append(i)
        elif 0 <= parent < i:
            children[parent].append(i)
        else:
            raise ValueError("invalid parent")
    def merge(left, right):
        combined = {}
        for a, u in left.items():
            for b, v in right.items():
                combined.setdefault(a ^ b, u | v)
        return combined
    tables = [None] * n
    for i in reversed(range(n)):
        choices = []
        for value in (0, 1):
            row = {labels[i] if value else 0: (1 << i) if value else 0}
            for child in children[i]:
                row = merge(row, tables[child][value])
            choices.append(row)
        tables[i] = tuple((choices[0] | choices[1]) if permit else choices[0]
                          for permit in allowed[i])
    row = {0: 0}
    for root in roots:
        row = merge(row, tables[root][0])
    return row.get(target)

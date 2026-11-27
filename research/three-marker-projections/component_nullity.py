"""Exact trace H (low two named bits), preserving zero-based physical IDs."""


def dependencies(columns):
    pivots = {}
    result = []
    for i, value in enumerate(columns):
        support = 1 << i
        while value:
            p = value.bit_length() - 1
            if p not in pivots:
                pivots[p] = value, support
                break
            v, s = pivots[p]
            value ^= v
            support ^= s
        else:
            result.append(support)
    return result


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def trace(private, named, support):
    ids = list(bits(support))
    space = {0}
    for relation in dependencies([private[i] for i in ids]):
        image = 0
        for j in bits(relation):
            image ^= named[ids[j]]
        space |= {x ^ image for x in space}
    return frozenset(space)


def witness(private, named):
    if len(private) != len(named):
        raise ValueError("column counts differ")
    # Fundamental circuits generate the private kernel. Overlapping circuits
    # belong to the same component; coloops contribute no trace.
    blocks = []
    for circuit in dependencies(private):
        merged = [circuit]
        support = circuit
        remaining = []
        for indices, basis in blocks:
            if indices & circuit:
                merged.extend(basis)
                support |= indices
            else:
                remaining.append((indices, basis))
        blocks = remaining + [(support, merged)]

    states = {frozenset({0}): 0}
    for _, basis in blocks:
        vectors = [0]
        for relation in basis:
            vectors.extend([v ^ relation for v in vectors])
        options = {}
        for i, y in enumerate(vectors):
            for j in range(i + 1):
                support = y | vectors[j]
                local = trace(private, named, support)
                if max(local) < 4:
                    options.setdefault(local, support)
        updated = {}
        for prev, chosen in states.items():
            for local, support in options.items():
                total = frozenset(x ^ y for x in prev for y in local)
                updated.setdefault(total, chosen | support)
        states = updated
    found = states.get(frozenset(range(4)))
    return None if found is None else list(bits(found))

"""Guard i = list of (constant bit, bitmask of predecessors) truth indicators."""


def forest_possible(guards, labels, target):
    n = len(guards)
    if len(labels) != n:
        raise ValueError("one marker vector required per vertex")
    owner = [None] * n
    children = []
    for i, literals in enumerate(guards):
        mask = 0
        for c, deps in literals:
            if c not in (0, 1) or deps < 0 or deps >> i:
                raise ValueError("invalid topological literal")
            mask |= deps
        child = []
        while mask:
            bit = mask & -mask
            v = bit.bit_length() - 1
            if owner[v] is not None:
                raise ValueError("a variable influences more than one guard")
            owner[v] = i
            child.append(v)
            mask ^= bit
        children.append(child)

    tables = []
    for i, literals in enumerate(guards):
        states = [set(), set()]
        for root in (0, 1):
            for constant, deps in (literals if root else [(1, 0)]):
                current = {(labels[i] if root else 0, constant)}
                for v in children[i]:
                    following = set()
                    for value in (0, 1):
                        parity = value & (deps >> v)
                        following.update((x ^ y, q ^ parity)
                                         for x, q in current for y in tables[v][value])
                    current = following
                states[root].update(x for x, q in current if q)
        tables.append(states)
    reached = {0}
    for v in range(n):
        if owner[v] is None:
            additions = tables[v][0] | tables[v][1]
            reached = {x ^ y for x in reached for y in additions}
    return target in reached

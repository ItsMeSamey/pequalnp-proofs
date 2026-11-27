"""Find a complete two-state reading order in an explicit weighted program."""
from boolean_value_automata import apply, dot, insert
from two_state_other_order import validate


def cofactor_values(program, order, pins, pivot, cost):
    """Output pairs on a sample spanning the affine hull of all paired runs."""
    dims, start, layers, final = program
    current = [(start, start)]
    for i, (var, layer) in enumerate(zip(order, layers)):
        choices = (pins[var],) if var in pins else (0, 1)
        if var == pivot:
            choices = (0,)
        basis = {}
        following = []
        for low, high in current:
            for bit in choices:
                u = apply(low, layer[bit])
                v = apply(high, layer[1 if var == pivot else bit])
                cost['candidate_pairs'] += 1
                key = 1 | (u << 1) | (v << (1 + dims[i+1]))
                if insert(basis, key, 0):
                    following.append((u, v))
        current = following
    return [(dot(u, final), dot(v, final)) for u, v in current]


def recognize(program, order):
    validate(program, order)
    pins, records = {}, []
    cost = {'variable_tests': 0, 'candidate_pairs': 0}
    remaining = list(order)
    while remaining:
        for variable in remaining:
            cost['variable_tests'] += 1
            pairs = cofactor_values(program, order, pins, variable, cost)
            low, high = map(set, zip(*pairs))
            parity = {x ^ y for x, y in pairs}
            identity = (1, 2)
            if len(low) == 1:
                fixed = 1 << next(iter(low))
                maps, keep = ((fixed, fixed), identity), 1
            elif len(high) == 1:
                fixed = 1 << next(iter(high))
                maps, keep = (identity, (fixed, fixed)), 0
            elif len(parity) == 1:
                maps, keep = (identity, (2, 1) if 1 in parity else identity), 0
            else:
                continue
            pins[variable] = keep
            records.append((variable, maps))
            remaining.remove(variable)
            break
        else:
            return None, None, cost
    state = program[1]
    for variable, layer in zip(order, program[2]):
        state = apply(state, layer[pins[variable]])
    initial = 1 << dot(state, program[3])
    records.reverse()
    output = ([2] * (len(order)+1), initial, [m for _, m in records], 2)
    return output, [v for v, _ in records], cost

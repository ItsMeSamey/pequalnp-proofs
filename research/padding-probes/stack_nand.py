"""NAND graph on physical key bits, with exact strict challenge and stack predictor."""
from itertools import product

from stack_padding import padding_dag


def nand_challenge(g):
    """Return the 4g strict clauses asserting y_i = NAND(a_i,b_i).

    Variables, in ascending physical key order, are the g pairs (a_i,b_i)
    followed by y_(g-1), ..., y_0. The enable bit follows all 3g variables.
    """
    if type(g) is not int or g < 1:
        raise ValueError("expected a positive number of NAND blocks")
    clauses = []
    for i in range(g):
        variables = (2 * i + 1, 2 * i + 2, 3 * g - i)
        for a, b in product((0, 1), repeat=2):
            # Wrong output is AND(a,b). Exactly this triple falsifies the clause.
            wrong = (a, b, a & b)
            clauses.append(tuple(-v if bit else v for v, bit in zip(variables, wrong)))
    return clauses


def nand_dag(g):
    """Return (edges, start, final) for every original encoding of this challenge."""
    return padding_dag(nand_challenge(g), 3 * g)


def nand_dpda(g):
    """Return (table, initial, bottom, outputs) in stack_probe's raw-byte format.

    On the exact fibre the output equals padding_cnf.predict. On all other
    byte strings the same total line scanner runs, without a DIMACS promise.
    The DFA skips header/challenge/carrier lines, and takes the sign of the
    first decimal literal on each marker line as its bit. It ignores the rest
    of that line. Exact syntax is enforced separately by the fibre DAG.
    """
    prefix_count = 1 + len(nand_challenge(g)) + 8
    n = 3 * g
    accept = ("accept",)
    reject = ("reject",)
    states = [("prefix", j) for j in range(prefix_count)]
    for i in range(n + 1):
        for carry in ((0, 1) if i < 2 * g and i % 2 else (0,)):
            states.append(("first", i, carry))
        for carry in ((0, 1) if i < 2 * g and not i % 2 else (0,)):
            states.append(("tail", i, carry))
    states.extend((accept, reject))
    ids = {state: i for i, state in enumerate(states)}

    def transition(state, top, byte):
        phase = state[0]
        if phase in ("accept", "reject"):
            return reject, "stay"
        if phase == "prefix":
            if byte != 10:
                return state, "stay"
            j = state[1] + 1
            return (("prefix", j) if j < prefix_count else ("first", 0, 0)), "stay"
        _, i, carry = state
        if phase == "tail":
            if byte != 10:
                return state, "stay"
            return (("first", i + 1, carry) if i < n else accept), "stay"
        bit = int(byte == 45)
        if not bit and not 49 <= byte <= 57:
            return reject, "stay"
        if i < 2 * g:
            if i % 2 == 0:
                return ("tail", i, bit), "stay"
            expected = 1 ^ (carry & bit)
            return ("tail", i, 0), "push", expected + 1
        if i < n and top == bit + 1:
            return ("tail", i, 0), "pop"
        if i == n and bit and top == 0:
            return ("tail", i, 0), "stay"
        return reject, "stay"

    table = {}
    for state in states:
        for top in (0, 1, 2):
            for byte in range(256):
                dest, *operation = transition(state, top, byte)
                table[ids[state], top, byte] = (ids[dest], *operation)
    outputs = {ids[state]: int(state == accept) for state in states}
    return table, ids[("prefix", 0)], 0, outputs

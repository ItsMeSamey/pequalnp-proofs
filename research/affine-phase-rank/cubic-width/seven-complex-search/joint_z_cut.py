"""Necessary seven-term G3 test using local commuting Z measurements."""
from itertools import combinations
from support_envelope import Envelope

PAIRS = tuple(combinations(range(1, 8), 2))


def forced_z(column):
    """Map (block, local Z mask) to a parity shared by the support envelope."""
    env = Envelope(9, column)
    # A constant nontrivial parity excludes half the quotient cosets.
    if len(env.forbidden) * 2 < 1 << (9 - len(env.pivots)):
        return {}
    points = [x for x in range(512) if env.rem(x) not in env.forbidden]
    if not points:
        # Even an identically zero column is safe to leave uncounted.
        return {}
    origin = points[0]
    result = {}
    for block in range(3):
        shift = 3 * block
        differences = {(x ^ origin) >> shift & 7 for x in points}
        for mask in range(1, 8):
            if all((d & mask).bit_count() % 2 == 0 for d in differences):
                result[block, mask] = ((origin >> shift) & mask).bit_count() % 2
    return result


def forced_x(column):
    """An affine basis of equal observed phase differences fixes an X sign."""
    if len(column) < 10 or -1 in column.values():
        return {}
    result = {}
    for block in range(3):
        for mask in range(1, 8):
            shift = mask << (3 * block)
            origin = None
            pivots = {}
            for x, phase in column.items():
                if (x ^ shift) not in column:
                    continue
                delta = (column[x ^ shift] - phase) % 4
                if origin is None:
                    origin = x
                    expected = delta
                if delta != expected or delta % 2:
                    break
                v = x ^ origin
                while v and v.bit_length() in pivots:
                    v ^= pivots[v.bit_length()]
                if v:
                    pivots[v.bit_length()] = v
                if len(pivots) == 9:
                    # A stabilizer phase derivative is constant plus twice a parity.
                    result[block, mask] = delta // 2
                    break
    return result


def outcome_conflict(signs):
    if sum(bool(s) for s in signs) < 4:
        return False
    for block in range(3):
        for p, q in PAIRS:
            for a in (0, 1):
                for b in (0, 1):
                    outcome = ((p, a), (q, b), (p ^ q, a ^ b))
                    killed = sum(any(s.get((block, m), bit) != bit for m, bit in outcome)
                                 for s in signs)
                    if killed >= 4:
                        return True
    return False


def rejects(columns):
    return (outcome_conflict([forced_z(c) for c in columns])
            or outcome_conflict([forced_x(c) for c in columns]))

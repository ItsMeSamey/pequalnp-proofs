"""Check the private OR-gate bound for matched pairs of residual rectangles."""
from collections import Counter
from functools import lru_cache


def _matchings(ids):
    if not ids:
        yield ()
        return
    i, *tail = ids
    for k, j in enumerate(tail):
        for rest in _matchings(tail[:k] + tail[k + 1:]):
            yield ((i, j),) + rest


def _bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def audit_private(covers, residual, free):
    """Return counts by overlap or decimal lower bound on private OR gates."""
    matchings = list(_matchings(range(10)))
    if len(matchings) != 945:
        raise ValueError("invalid matching enumeration")
    atoms = tuple((1 << u, 1 << v) for u, v in residual)
    bank = tuple(free)
    hist = Counter()

    @lru_cache(maxsize=8192)
    def free_pieces(required, allowed):
        return frozenset(required & p for p in bank if not p & ~allowed)

    @lru_cache(maxsize=32768)
    def private(required, pieces):
        if not required:
            return 0
        # Dominated frontier pieces can be replaced by a superset at equal cost.
        maximal = []
        for piece in sorted(pieces, key=int.bit_count, reverse=True):
            if piece and not any(piece & q == piece for q in maximal):
                maximal.append(piece)
        supports = sorted((tuple(p for p in maximal if b & p), b)
                          for b in _bits(required))
        supports.sort(key=lambda entry: len(entry[0]))
        if not supports[0][0]:
            raise ValueError("mandatory atom lacks a frontier piece")

        @lru_cache(None)
        def count(rem):
            if not rem:
                return 0
            choices = next(ps for ps, b in supports if rem & b)
            return 1 + min(count(rem & ~p) for p in choices)

        # Joining k frontier pieces takes at least k-1 private binary ORs.
        try:
            return count(required) - 1
        finally:
            count.cache_clear()

    try:
        for rects in covers:
            if len(rects) != 10:
                raise ValueError("expected ten rectangles")
            must = [[0, 0] for _ in rects]
            for row, col in atoms:
                owners = [i for i, (r, c) in enumerate(rects) if r & row and c & col]
                if not owners:
                    raise ValueError("cover omits residual atom")
                if len(owners) == 1:
                    owner = must[owners[0]]
                    owner[0] |= row
                    owner[1] |= col
            ends = {}
            for i in range(10):
                for j in range(i + 1, 10):
                    if must[i][0] & must[j][0] or must[i][1] & must[j][1]:
                        continue
                    ends[i, j] = tuple(
                        (rects[a][0] | rects[b][1] << 32,
                         must[a][0] | must[b][1] << 32)
                        for a, b in ((i, j), (j, i)))
            for pairs in matchings:
                if any(pair not in ends for pair in pairs):
                    hist["overlap"] += 1
                    continue
                endpoints = [e for pair in pairs for e in ends[pair]]
                cost = 0
                for i, (allowed, required) in enumerate(endpoints):
                    # A shared subexpression reaches another endpoint. Its
                    # contribution fits inside that endpoint's allowed mask.
                    shared = frozenset(required & a for j, (a, _) in enumerate(endpoints)
                                       if i != j)
                    cost += private(required, shared | free_pieces(required, allowed))
                hist[str(cost)] += 1
    finally:
        private.cache_clear()
        free_pieces.cache_clear()
    return dict(hist)

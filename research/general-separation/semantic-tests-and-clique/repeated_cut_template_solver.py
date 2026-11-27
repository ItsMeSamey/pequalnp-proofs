"""Repeated low-rank reductions with original-label witness recovery.

CLI: pass {"adjacency":[integer masks],"pins":[i,j,k]} on standard input.
The adjacent modules supplied_cut_reducer and three_pin_template_solver are required.
"""
import argparse
import json
import sys
from itertools import combinations
from random import Random
from supplied_cut_reducer import bits, graphs, reduce_cut
from three_pin_template_solver import solve as template_solve


def find_cut(A, pins):
    n = len(A)
    if n <= 3:
        return None
    vertices = range(n)
    full = (1 << n)-1
    pinmask = sum(1 << i for i in pins)
    for k in range(3):
        for I in combinations(vertices,k):
            left = sum(1 << i for i in I)
            for J in combinations((i for i in vertices if not left >> i & 1),k):
                right = sum(1 << j for j in J)
                # Reconstruct each row from its entries on J. Full span of these
                # patterns is equivalent to nonsingularity of the anchor minor.
                combinations_map = {0: 0}
                for i in I:
                    combinations_map.update({pattern ^ (A[i]&right): row ^ A[i]
                                             for pattern,row in combinations_map.items()})
                if len(combinations_map) != 1 << k:
                    continue
                # For every mismatch v,w add v -> w. Scan predecessor rows to
                # compute all vertices forced outside by implication closure.
                mismatch = [row ^ combinations_map[row&right] for row in A]
                for allowed in ([None] if k == 2 else [None,*pins]):
                    required = left | (0 if allowed is None else 1 << allowed)
                    outside = right | (pinmask & ~(0 if allowed is None else 1 << allowed))
                    if required & outside:
                        continue
                    queue = list(bits(outside))
                    for w in queue:
                        for v in vertices:
                            if not outside >> v & 1 and mismatch[v] >> w & 1:
                                outside |= 1 << v
                                queue.append(v)
                    side = full ^ outside
                    if side.bit_count() >= 4 and required & side == required:
                        return list(bits(side))
    return None


def preprocess(A,pins):
    """Return residual rows, residual pins and lifts in chronological order."""
    lifts = []
    while True:
        side = find_cut(A,pins)
        if side is None:
            return A,pins,lifts
        old_n = len(A)
        A,pins,lift = reduce_cut(A,side,pins)
        assert len(A) < old_n
        lifts.append(lift)


def solve(A,pins):
    n = len(A)
    if (not isinstance(pins,(list,tuple)) or len(pins) != 3 or
            any(type(i) is not int or not 0 <= i < n for i in pins) or len(set(pins)) != 3):
        raise ValueError("provide three distinct integer pin indexes")
    if any(type(row) is not int or not 0 <= row < 1 << n for row in A):
        raise ValueError("invalid adjacency masks")
    if any(row >> i & 1 or any((row >> j & 1) != (A[j] >> i & 1) for j in range(i))
           for i,row in enumerate(A)):
        raise ValueError("adjacency must be symmetric and loopless")
    B,Q,lifts = preprocess(A,pins)
    w = template_solve(B,Q)
    if w is not None:
        for lift in reversed(lifts):
            w = lift(w)
        assert all(w >> i & 1 for i in pins)
        assert all(not ((A[i]&w).bit_count()%2) for i in bits(w))
    return w


def admissible(A,pins,mask):
    count = sum(mask >> p & 1 for p in pins)
    if mask.bit_count() < 4 or count > 1:
        return False
    space = {0}
    for i in bits(mask):
        space |= {u ^ (A[i] & ~mask) for u in space}
    return len(space) <= (4 if count == 0 else 2)


def self_test():
    rng = Random(433)
    count = 0
    def compare(A,pins):
        side = find_cut(A,pins)
        exists = any(admissible(A,pins,m) for m in range(1 << len(A)))
        assert (side is not None) == exists
        if side is not None:
            assert admissible(A,pins,sum(1 << i for i in side))
    for n in (3,4,5):
        for A in graphs(n):
            compare(A,[0,1,2])
            count += 1
    for n in range(6,10):
        for _ in range(25):
            A = [0]*n
            for i,j in combinations(range(n),2):
                if rng.randrange(2):
                    A[i] |= 1 << j
                    A[j] |= 1 << i
            pins = rng.sample(range(n),3)
            compare(A,pins)
            w = solve(A,pins)
            assert (w is not None) == any(all(s >> p & 1 for p in pins) and
                all(not ((A[i]&s).bit_count()%2) for i in bits(s)) for s in range(1 << n))
            count += 1
    # Three disconnected pinned stars require the center and an even number of
    # selected leaves. Side replacements can include previous gadget vertices.
    n = 15
    A = [0]*n
    for c in (0,5,10):
        for i in range(c+1,c+5):
            A[c] |= 1 << i
            A[i] |= 1 << c
    B,Q,lifts = preprocess(A,[0,5,10])
    assert len(lifts) >= 2
    w = solve(A,[0,5,10])
    assert w is not None
    connected = [18,5,34,32,257,140,384,96,80]
    residual, retained, chain = preprocess(connected, [0,1,2])
    assert len(chain) == 2
    from supplied_cut_reducer import valid
    originals = valid(connected, [0,1,2])
    assert 7 not in originals and originals
    for candidate in valid(residual, retained):
        for lift in reversed(chain):
            candidate = lift(candidate)
        assert candidate in originals
    assert solve(connected,[0,1,2]) in originals
    print(count,"finder comparisons; nested stages",len(lifts),"witness",w)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test",action="store_true")
    if parser.parse_args().self_test:
        self_test()
    else:
        if hasattr(sys,"set_int_max_str_digits"):
            sys.set_int_max_str_digits(0)
        data = json.load(sys.stdin)
        print(json.dumps({"witness":solve(data["adjacency"],data["pins"])}))

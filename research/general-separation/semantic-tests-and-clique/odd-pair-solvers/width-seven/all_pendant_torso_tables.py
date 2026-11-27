"""Verify all 16 physical states for each rooted leaf-torso presentation."""

from collections import Counter
from degree_five_terminal_sweep import closed_root
from eleven_limb_response import table
import mixed_torso_full_census as mixed


def run():
    receipts = Counter()

    def record(rows):
        assert len(rows) in (6, 7, 11)
        for has_edge in (False, True):
            graph = list(rows)
            if bool(graph[0] & 2) != has_edge:
                graph[0] ^= 2
                graph[1] ^= 1
            assert all(x > 0 for row in table(graph) for x in row)
        receipts[len(rows)] += 1

    for c in (1, 2, 3):
        for g in closed_root(c, 3 - c, 3 - c):
            assert g[0].bit_count() == g[1].bit_count() == 3
            record(g)
    direct = mixed.unique_full

    def collect(rows):
        if not direct(rows):
            return False
        record(rows)
        return True

    mixed.unique_full = collect
    try:
        mixed.main()
    finally:
        mixed.unique_full = direct
    assert receipts == {6: 4, 7: 12, 11: 48}
    print("Both boundary-edge states:", sorted(receipts.items()))


if __name__ == "__main__":
    run()

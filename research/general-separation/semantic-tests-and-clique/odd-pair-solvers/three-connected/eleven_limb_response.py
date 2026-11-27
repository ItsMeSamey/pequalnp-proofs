"""Check the original two-port table on every enumerated 11-site presentation."""

from mixed_torso_full_census import main
import mixed_torso_full_census as census


def table(rows):
    counts = [[0] * 4 for _ in range(4)]
    for word in range(1 << len(rows)):
        if any(
            word >> i & 1 and (rows[i] & word).bit_count() % 2 == 0
            for i in range(2, len(rows))
        ):
            continue
        for drift in range(4):
            if all(
                not word >> i & 1
                or ((rows[i] & word).bit_count() + ((drift >> i) & 1)) % 2
                for i in range(2)
            ):
                row = counts[word & 3]
                row[drift] = min(2, row[drift] + 1)
    return counts


def run():
    receipts = []
    original = census.unique_full

    def check(rows):
        if not original(rows):
            return False
        if len(rows) == 11:
            physical = rows[:]
            physical[0] ^= 2
            physical[1] ^= 1
            counts = table(physical)
            assert counts == [[2, 2, 2, 2], [2, 2, 2, 2], [2, 2, 2, 2], [2, 2, 1, 2]]
            receipts.append(1)
        return True

    census.unique_full = check
    try:
        main()
    finally:
        census.unique_full = original
    assert len(receipts) == 48
    print("48 native two-port tables checked")


if __name__ == "__main__":
    run()

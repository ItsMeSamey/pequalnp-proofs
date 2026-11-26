"""Check the four-pure cover against the original decorated census."""
from collections import Counter
from pathlib import Path

root = Path(__file__).resolve().parent
rows = [tuple(map(int, line.split())) for line in (root / "rows").read_text().splitlines()]
two_clean = {tuple(map(int, line[2:].split("|")[0].split()))
             for line in (root / "clean2.log").read_text().splitlines() if line.startswith("X ")}
counts = Counter()
used_two_clean = set()
assert len(rows) == len(set(rows)) == 351
for p, graph, clean, branch, quartet, dirty in rows:
    row = (p, graph, clean, branch, quartet, dirty)
    assert p == 4
    if quartet and branch & ~quartet:
        case = "inherited quartet"
    elif quartet == 0 and branch.bit_count() >= 3:
        assert dirty == 0 and clean.bit_count() + branch.bit_count() == 4
        case = "exit count"
    elif graph == 52 and quartet == 15:
        case = "quartet triangle"
    else:
        assert clean.bit_count() == 2 and row in two_clean
        used_two_clean.add(row)
        case = "two-clean closure"
    counts[case] += 1
assert counts == {"inherited quartet":195, "exit count":80, "quartet triangle":14, "two-clean closure":62}
assert used_two_clean == two_clean
for name, count in counts.items():
    print(name, count)

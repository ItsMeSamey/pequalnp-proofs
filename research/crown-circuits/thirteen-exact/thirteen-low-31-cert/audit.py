from pathlib import Path

root = Path(__file__).resolve().parent


def rows(name):
    return [tuple(map(int, line.split())) for line in (root / name).read_text().splitlines()]


for ledger, targets in [('full4-min.tsv','all4.txt'),('low4.tsv','hard4.txt'),('low5.tsv','hard5.txt')]:
    outputs = rows(ledger)
    expected = rows(targets)
    assert sorted(r[0] for r in outputs) == sorted(r[0] for r in expected)
    assert all(len(r) == 4 and r[3] == 0 for r in outputs)
    by_id = dict((r[0], r[1:]) for r in expected)
    for ident, atoms, _, _ in outputs:
        activation = by_id[ident]
        features = set()
        for word in range(1 << len(activation)):
            features.add(tuple(((word >> j) & 1) if ((u >> word) & 1) else -1
                               for j, u in enumerate(activation)))
        assert len(features) == atoms
    print(ledger, len(outputs), sum(r[2] for r in outputs), 'zero packings')

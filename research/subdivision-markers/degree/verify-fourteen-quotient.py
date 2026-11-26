from itertools import combinations
from pathlib import Path

records = Path(__file__).with_name('fourteen-quotient.txt').read_text().splitlines()
for record in records:
    header, points = record.split(':')
    h, success, *rows = map(int, header.split())
    clique = list(map(int, points.split()))
    assert success and len(set(clique)) == 9
    matrix = [row | (32 if i < h else 64) for i, row in enumerate(rows)] + [31]
    ends = [64 * 128 + 96, 63 * 128 + 31]
    def raw(v):
        x, y = divmod(v, 128)
        return (all(not (x >> i & 1) or (row & y).bit_count() % 2 == 0
                    for i, row in enumerate(matrix))
                and all(not (y >> j & 1) or sum((x >> i & 1) * (row >> j & 1)
                        for i, row in enumerate(matrix)) % 2 == 0 for j in range(7)))
    assert all(raw(v) for v in ends)
    for a, b in combinations(clique, 2):
        for v in (a ^ b, a ^ b ^ 16383):
            assert v and any(raw(v ^ w) for w in ends)
print(f'{len(records)} certificates verified')

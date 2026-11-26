"""Replay all four-star orbits from the encoded residual samples."""
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import argparse
import re
import subprocess
import tempfile
from samples import actions, raw_samples

HERE = Path(__file__).resolve().parent
MASK = 8191


def four_groups(family, chosen):
    possible = {0}
    for target in chosen:
        eligible = [i for i, signature in enumerate(family) if signature & target == target]
        outside = [i for i in range(13) if not (target >> i & 1)]
        pairs = [(1 << i) | (1 << j) for i, j in combinations(outside, 2)]
        covering = []
        for size in range(1, len(eligible) + 1):
            for group in combinations(eligible, size):
                used = sum(1 << i for i in group)
                if any(prev & used == prev for prev in covering):
                    continue
                if all(any(not family[i] & pair for i in group) for pair in pairs):
                    covering.append(used)
        possible = {old | add for old in possible for add in covering if not old & add}
    return bool(possible)


def check_records(quartet, chosen, largest, banks, evidence):
    records = [tuple(map(int, r.split())) for r in evidence.splitlines()]
    families = [tuple(map(int, r.split())) for r in banks.splitlines()]
    assert families == [x[:11] for x in records]
    for family in set(families):
        assert len(set(family)) == 11 and four_groups(family, chosen)
        private = set()
        for a, b in largest:
            covering = [x for x in family if x & a and not x & b]
            assert covering
            if len(covering) == 1:
                private.add(covering[0])
        assert len(private) == 11
    assert all(x[11] == -1 and x[-1] == 0 for x in records)
    digest = sha256(('\n'.join(' '.join(map(str, fam)) for fam in sorted(set(families)))
                     + '\n').encode()).hexdigest()
    result = f'{quartet} {len(records)} {len(set(families))} {digest}'
    known = {int(line.split()[0]): line for line in (HERE / 'expected.txt').read_text().splitlines()}
    assert result == known[quartet]
    print(result, flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('quartets', nargs='*', type=int, help='optional subset of the five orbits')
    options = parser.parse_args()
    positives, negatives = raw_samples(HERE / 'L-meta-18968.json')
    sample_actions = actions(positives, negatives)
    stars = [sum(1 << ((q + d) % 13) for d in (0, 1, 3, 9)) for q in range(6, 13)]
    for j, target in enumerate(stars):
        outside = [(1 << x) | (1 << y) for x, y in combinations(range(13), 2)
                   if not target & ((1 << x) | (1 << y))]
        for left, right in combinations([s for s in stars if s != target], 2):
            candidates = [n & MASK for n in negatives if n >> (13 + j) & 1
                          and n & left and n & right]
            assert all(any(not (pair & ~q) for q in candidates) for pair in outside)
    assert all(any(not (((1 << a) | (1 << b)) & ~n) for n in negatives)
               for a, b in combinations(range(13), 2))
    reps = sorted({min(sum(1 << stars.index(action[stars[i]]) for i in quartet)
                           for action in sample_actions)
                   for quartet in combinations(range(7), 4)})
    assert reps == [15, 23, 27, 46, 83]
    raw = {1 << i for i in range(13)}
    for q in range(6):
        first = (1 << q) | (1 << ((q + 1) % 13))
        second = (1 << ((q + 3) % 13)) | (1 << ((q + 9) % 13))
        raw.update([first, second, first | second])
    relaxed = sorted({perm[x] for perm in sample_actions for x in raw})
    header = (HERE / 'hereditaryrole.hpp').read_text()
    assert len(relaxed) == 55
    literal = re.search(r'orbitraw\[\]\s*=\s*\{([^}]+)\}', header, re.DOTALL)
    assert literal and [int(x) for x in literal[1].split(',')] == relaxed
    rows = {(a & MASK, b & MASK) for a in positives for b in negatives
            if not ((a >> 13) & ~(b >> 13))}
    largest = sorted((a, b) for a, b in rows
                     if not any(c == a and b != d and not b & ~d for c, d in rows))
    assert len(largest) == 1323 and all(a.bit_count() == 1 for a, _ in largest)
    with tempfile.TemporaryDirectory() as dirname:
        work = Path(dirname)
        samples = work / 'mixed.in'
        samples.write_text(f'{len(positives)} {len(negatives)}\n'
                           + ' '.join(map(str, sorted(positives))) + '\n'
                           + ' '.join(map(str, sorted(negatives))) + '\n')
        # The driver reads seven historical anchor pairs before loading the verified pair clique.
        bank_data = ' '.join(map(str, stars)) + '\n' + '0 0\n' * 7
        bank_data += ''.join(f'{a} {b}\n' for a, b in largest)
        for source in ('stream11simple', 'mixed11'):
            subprocess.run(['c++', '-O3', '-std=c++20', '-march=native',
                            HERE / f'{source}.cpp', '-o', work / source], check=True)
        requested = options.quartets or reps
        assert set(requested) <= set(reps)
        for quartet in requested:
            anchors = HERE / f'pairanchors-{quartet}.txt'
            clique = [tuple(map(int, line.split())) for line in anchors.read_text().splitlines()]
            chosen = {t for i, t in enumerate(stars) if quartet >> i & 1}
            assert len(clique) == 7 and {p for p, _ in clique[:4]} == chosen
            assert all(not (a & b) and b.bit_count() == 2 for a, b in clique[:4])
            assert all(row in largest for row in clique[4:])
            assert all(bool(a & d or c & b) for (a, b), (c, d) in combinations(clique, 2))
            banks = work / 'banks.txt'
            with banks.open('w') as output:
                subprocess.run([work / 'stream11simple', str(quartet), anchors],
                               input=bank_data, text=True, stdout=output, check=True)
            evidence = subprocess.run([work / 'mixed11', samples, banks, '10000', '1'],
                                      stdout=subprocess.PIPE, text=True, check=True).stdout
            check_records(quartet, chosen, largest, banks.read_text(), evidence)


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run the verifier with Python assertions enabled.')
    main()

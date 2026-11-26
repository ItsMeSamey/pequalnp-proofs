"""Reconstruct the signature constraints and check the saved enumerator input."""
from pathlib import Path
from verify_mixed import coords, front, target, sets

base = Path(__file__).resolve().parent
canonical = [sum(1 << ((j+6+d)%13) for d in (0,1,3,9)) for j in range(7)]
rows = [coords(i) for i in range(676)]
obligations = sorted({(p,n) for i,(p,l) in enumerate(rows) if (target^front) >> i & 1
                      for j,(n,k) in enumerate(rows) if not target >> j & 1 and not l & ~k})
maximal = [(a,b) for a,b in obligations
           if not any(a == c and b != d and not b & ~d for c,d in obligations)]
anchors = [(rows[p][0], rows[n][0]) for p,n in sets['point']]
if __name__ == '__main__':
    expected = [canonical, *anchors, *maximal]
    actual = [list(map(int,s.split())) for s in (base/'raw.in').read_text().splitlines()]
    if actual != [list(line) for line in expected]:
        raise ValueError('the enumerator input differs from the decoded theorem')
    print(f'{len(obligations)} raw obligations and {len(maximal)} maximal obligations')

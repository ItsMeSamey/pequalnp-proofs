"""Reconstruct all nine-gate banks in the six-selected-nonraw case."""
from input import point_obligations
from pathlib import Path
import sys

raw, rows = point_obligations(Path(sys.argv[1]))
stars = [sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
# Every qualifying six-tuple has three pairs and three triples from distinct stars.
# Remaining obligations give a finite hitting-set problem on the 31 raw masks.
def raw_completions(masks):
    clauses = {sum(1<<i for i,m in enumerate(raw) if m&p and not m&n)
               for p,n in rows if not any(m&p and not m&n for m in masks)}
    minimal = []
    for c in sorted(clauses, key=int.bit_count):
        if not any(c&m==m for m in minimal):
            minimal.append(c)
    found = set()
    def search(chosen):
        missed = next((c for c in minimal if not c&chosen), None)
        if missed is None:
            found.add(chosen)
        elif chosen.bit_count() < 5:
            for i in range(len(raw)):
                if missed>>i&1:
                    search(chosen | (1<<i))
    search(0)
    assert all(v.bit_count() == 5 for v in found)
    return found

if __name__ == '__main__':
    tuples=[tuple(map(int,l.split())) for l in Path(sys.argv[2]).read_text().splitlines()]
    out=[]
    for t in tuples:
        if sorted(m.bit_count() for m in t) != [2,2,2,3,3,3]:
            continue
        choices=raw_completions(t)
        assert len(choices)==1
        chosen=choices.pop()
        bank=tuple(sorted((*t,*(m for i,m in enumerate(raw) if chosen>>i&1))))
        assert sum(m.bit_count()==1 for m in bank)==5
        out.append(bank)
    assert len(set(out))==24
    for bank in sorted(set(out)):
        print(*bank)

"""Check that all relaxed-positive profiles enter both chronological replays."""
from pathlib import Path
import sys
def rows(path):
    return [row.split() for row in Path(path).read_text().splitlines()]
profiles, ledger, dynamic, static = map(rows, sys.argv[1:])
assert len(profiles) == len(ledger) == 25721
assert [int(r[0]) for r in ledger] == list(range(25721))
needed = [int(r[0]) for r in ledger if int(r[4])]
assert [int(r[0]) for r in dynamic] == [int(r[0]) for r in static] == needed
assert all(int(r[2]) == 0 for r in dynamic)
assert all(int(r[1]) == 0 for r in static)
total=sum(int(r[3]) for r in ledger)
print(len(ledger), 'profiles', total, 'relaxed helper libraries,', len(needed), 'late cases')
print(sum(int(r[1]) for r in dynamic), 'forward states; bank-first replay checked',
      sum(int(r[2]) for r in static), 'banks, including', sum(int(r[3]) for r in static), 'realizable banks')

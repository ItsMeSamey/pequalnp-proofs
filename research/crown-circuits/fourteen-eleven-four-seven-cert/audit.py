"""Read the archived ledgers and map all 411 host pairs and all 28 branch marks."""
import csv
from collections import Counter
from pathlib import Path
root=Path(__file__).resolve().parent
def records(p):
    with (root/p).open() as f:
        return list(csv.DictReader(f, delimiter='\t'))
rows=[r for r in records('degree/t14-34/eleven-atlas.tsv') if r['orders']=='4,7']
assert len(rows)==len({r['graphs'] for r in rows})==411
by=Counter()
exceptions=set()
for r in rows:
    small=int(r['edge_counts'].split(',')[0])
    floor=int(r['local_OR_floors'].split(',')[1])
    if floor>=6:
        by['physical remote' if small<=4 else 'four lost ORs']+=1
    else:
        exceptions.add(r['graphs'])
assert by=={'physical remote':276,'four lost ORs':131}
assert exceptions=={f'G18,G{g}' for g in (446,447,448,450)}
marks=records('comb/fourteen-construct/eleven-marked-branches.tsv')
assert {(int(r['large_graph']),int(r['branch'])) for r in marks}=={(g,x) for g in (446,447,448,450) for x in range(7)}
cases=Counter(r['remaining_components'] for r in marks)
assert cases=={'connected-cubic':18,'P6':2,'C6':3,'C3+P3':1,'C4+K2':1,'K2+paw':2,'C3+C3':1}
print(f'{len(rows)} hosts = 276 physical + 131 four-flag + 4 marked. {len(marks)} marks = 18 cubic + 2 path + 3 cycle + 3 isolated-edge + 2 triangle.')

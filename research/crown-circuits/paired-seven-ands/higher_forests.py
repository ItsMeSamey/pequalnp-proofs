from singleton_forests import forests
from pathlib import Path
from sys import argv
for d in (4,5,6):
    out=Path(argv[1])/f'forest-{d}.tsv'
    with out.open('w') as f:
        for i,(tree,dest) in enumerate(sorted(forests(d).items())):
            from forest_capacity import capacity
            from math import prod
            print(i,0,prod(map(capacity,tree)),*(1<<x for x in dest),file=f)

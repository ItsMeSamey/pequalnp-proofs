"""Physical separation of plain intersections from XOR of two intersections."""
from itertools import combinations
from four_minor_pair_filters import accepts,pairs,trace

columns=(39,102,80,50,116,11,108,91,43)
attained={trace(columns,idx) for idx in combinations(range(len(columns)),5)}-{0}
assert len(attained)==23 and 1 not in attained
assert all(any(accepts(q,p) for p in attained) for q in pairs)
a,b=(1,40),(31,45)
assert accepts(a,1)!=accepts(b,1)
assert all(accepts(a,p)==accepts(b,p) for p in attained)
print('private rank 3, 23 attained decoys, 136 ordinary pairs blocked; XOR separates target')

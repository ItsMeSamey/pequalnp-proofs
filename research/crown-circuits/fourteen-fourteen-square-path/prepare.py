"""Stage the C4+P4 graph using the archived graph-cut OR-only encoding."""
from pathlib import Path
from itertools import combinations
here=Path(__file__).resolve().parent
edges=[(0,1),(1,2),(2,3),(3,0),(4,5),(5,6),(6,7)]
mask=sum(1<<(max(a,b)*(max(a,b)-1)//2+min(a,b)) for a,b in edges)
def decoder(x):
    a,b,c,d,e,f,g,h=[bool(x>>i&1) for i in range(8)]
    # Two local positive detectors and a cross-component detector.
    local1=(a and c) or (b and d)
    local2=(e and g) or (f and h)
    cross=(a or c) and (f or g)
    return local1 or local2 or cross
for choice in range(1<<len(edges)):
    x=0
    for i,(a,b) in enumerate(edges):
        if choice>>i&1:x|=1<<a|1<<b
    assert decoder(x)==(choice.bit_count()>=2)
(here/'query.tsv').write_text(f'8 {mask} 5\n')
print(f'graph {mask}; six ORs verified on all 128 raw selections; 7 negative edges and 21 pair tests.')

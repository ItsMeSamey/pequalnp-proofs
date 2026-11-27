"""Generate single-profile planted receiver controls."""
from pathlib import Path
import sys
dest=Path(sys.argv[1]);dest.mkdir(exist_ok=True)
for d in (4,5):
    pairs=[(i,j) for i in range(4) for j in range(i+1,4)] if d==4 else [(i,(i+1)%5) for i in range(5)]
    words=range(16) if d==4 else [w for w in range(32) if w.bit_count()%2==0]
    witnesses=[]
    for w in words:
        hit=[(w>>i)&1 for i in range(d)] + [not(w>>i&1 and w>>j&1) for i,j in pairs]
        witnesses.append(sum(1<<i for i,v in enumerate(hit) if not v))
    assert len(set(witnesses))==16
    p=Path(f'outer5d{d}.cpp');s=p.read_text()
    lo=s.index('int mis[]=');hi=s.index(';',lo)
    (dest/p).write_text(s[:lo]+'int mis[]={'+','.join(map(str,witnesses))+'}'+s[hi:])
    p=Path(f'outer5d{d}core.inc');s=p.read_text()
    if d==4:s=s.replace('extensions++;','extensions++;stop=true;return;')
    (dest/p).write_text(s)

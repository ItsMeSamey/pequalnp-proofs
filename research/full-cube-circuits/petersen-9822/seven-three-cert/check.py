from pathlib import Path
import re
for k,n in [('forest3-run',11),('single-paid-run',177),('repeat-paid-run',21)]:
    for d in (2,3,4):
        receipts=[]
        for f in Path(k).glob(f'd{d}*.log'):
            for s in f.read_text().splitlines():
                m=re.fullmatch(r'(\d+) atoms .* hits (\d+)',s)
                if m:receipts.append((int(m[1]),int(m[2])))
        assert sorted(receipts)==[(i,0) for i in range(n)]
print('627 profile and direct-quota checks')

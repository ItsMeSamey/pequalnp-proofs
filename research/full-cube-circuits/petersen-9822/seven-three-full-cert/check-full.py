import gzip,re
from pathlib import Path
total=0
for k,n in [('forest3-run',11),('single-paid-run',177),('repeat-paid-run',21),('two-paid-run',2082),('three-paid-run',15201)]:
    for d in (2,3,4):
        a=[]
        for p in Path(k).glob(f'd{d}*.log*'):
            lines=(gzip.open(p,'rt').read() if p.suffix=='.gz' else p.read_text()).splitlines()
            for l in lines:
                m=re.fullmatch(r'(\d+) atoms .* hits (\d+)',l)
                if m:a.append((int(m[1]),int(m[2])))
        assert sorted(a)==[(i,0) for i in range(n)],(k,d)
        total+=len(a)
print(total,'profile and direct-quota checks')

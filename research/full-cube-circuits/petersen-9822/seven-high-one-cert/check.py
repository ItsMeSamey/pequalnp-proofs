from pathlib import Path
import re,gzip
total=0
for k,n in [('higher-zero-run',328),('higher-one-run',8193)]:
    for d in (2,3,4):
        ids=[]
        for p in Path(k).glob(f'd{d}*.log.gz'):
            for line in gzip.open(p,'rt'):
                m=re.fullmatch(r'(\d+) atoms (\d+)(?: .* hits (\d+)| excluded)',line.strip())
                assert m
                assert m[3]=='0' if m[3] is not None else int(m[2])<16
                ids.append(int(m[1]))
        assert sorted(ids)==list(range(n))
        total+=len(ids)
print(total,'profile/quota pairs checked')

import re,gzip
from pathlib import Path
collected={}
for record in Path('completed-stages.tsv').read_text().splitlines():
    group,id,low,high,solver=record.split()
    expected=list(range(int(low),int(high)))
    got=[]
    for line in gzip.open(f'{group}-{id}.log.gz','rt'):
        m=re.fullmatch(r'(\d+) atoms (\d+)(?: .* hits (\d+)| excluded)',line.strip())
        assert m and (m[3]=='0' if m[3] is not None else int(m[2])<16)
        got.append(int(m[1]))
    assert got==expected
    collected.setdefault((group,id[:2]),[]).extend(got)
for (grp,q),ids in collected.items():
    assert sorted(ids)==list(range({'c5':55484,'c6':67349}[grp]))
assert len(collected)==6
print(sum(map(len,collected.values())),'negative profile/quota pairs')

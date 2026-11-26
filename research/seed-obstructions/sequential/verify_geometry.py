"""Read the pinned 676-column theorem and verify all negative extensions used."""
import hashlib
import json
import re
from itertools import combinations
from pathlib import Path
source=json.loads(Path(__file__).with_name('L-meta-18968.json').read_text())['formal_statement']
assert hashlib.sha256(source.encode()).hexdigest()=='d5fbefe3ea85033034056aae8ed0b90ecfe428b8a69e3456176309d0c82b54c2'
blocks=re.findall(r'\[((?:\(\d+ : ℕ\)(?:, )?)+)\]',source)
assert len(blocks)==2
columns=[]
for block in blocks:
    n=0
    for s in re.findall(r'\((\d+) : ℕ\)',block):n=n*10**19+int(s)
    for j in range(13):
        vals=[]
        for i in range(0,676,13):
            lane=(n>>i)&8191
            vals.append(((lane<<j)|(lane>>(13-j)))&8191)
        columns.append(sum(v<<(13*i) for i,v in enumerate(vals)))
target=int(re.search(r'x1 \(88 : ℕ\) = \((\d+) : ℕ\)',source)[1])
lines=[sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
def mask(k,ids):
    return sum(((columns[x]>>k)&1)<<i for i,x in enumerate(ids))
neg={(mask(k,range(13)),mask(k,range(19,26))) for k in range(676) if not target>>k&1}
pairs=[(1<<i)|(1<<j) for i,j in combinations(range(13),2)]
for X in pairs:
    for U in lines:
        assert any(not X&~q and q&U for q,_ in neg)
checked=0
for j,T in enumerate(lines):
    for i,U in enumerate(lines):
        if j==i:continue
        for k,V in enumerate(lines):
            if k==j or k==i:continue
            for a,b in combinations([x for x in range(13) if U>>x&1 and not T>>x&1],2):
                markers=(1<<a)|(1<<b)
                qs=[q for q,l in neg if l>>j&1 and q&markers and q&V]
                for X in pairs:
                    if not (X&T):assert any(not X&~q for q in qs)
                checked+=1
assert checked==630
print("Verified all 546 zero-line pair extensions and 630 line/marker choices, 36 outside pairs each.")

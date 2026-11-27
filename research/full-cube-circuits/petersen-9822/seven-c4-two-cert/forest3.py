"""Generate seven-switch signed literal activation forests with four full roots."""
from itertools import combinations_with_replacement
from functools import cache
from pathlib import Path
@cache
def forests(n):
    if n==0:return [()]
    out=set()
    for k in range(1,n+1):
        for t in trees(k):
            for rest in forests(n-k):
                out.add(tuple(sorted((t,)+rest)))
    return sorted(out)
@cache
def trees(n):
    out=set()
    for k in range(n):
        for a in forests(k):
            for b in forests(n-1-k):
                out.add(tuple(sorted((a,b))))
    return sorted(out)
def model(f):
    F=(1<<128)-1
    halves=[sum(1<<p for p in range(128) if p>>j&1) for j in range(7)]
    ready=[(t,F) for t in f];row=[]
    for j,(tree,u) in enumerate(ready):
        row.append(u)
        for b,sub in enumerate(tree):
            ready.extend((t,u&(halves[j] if b else F^halves[j])) for t in sub)
    assert len(row)==7 and row.count(F)==4
    return row
if __name__=='__main__':
    rows=[model(f) for f in forests(7) if len(f)==4]
    Path('forests3.tsv').write_text(''.join(' '.join(map(str,u))+'\n' for u in rows))
    print(len(rows))

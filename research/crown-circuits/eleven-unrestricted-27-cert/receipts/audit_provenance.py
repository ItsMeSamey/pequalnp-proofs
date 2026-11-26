"""Check each merged row against its designated source and any necessary exact replay."""
from pathlib import Path
from collections import defaultdict
import argparse,json
p=argparse.ArgumentParser(); p.add_argument('source',type=Path);p.add_argument('logs',type=Path)
p.add_argument('--complete',action='store_true');p.add_argument('--save',type=Path);a=p.parse_args()
def nums(path):
    return [tuple(map(int,r.split())) for r in path.read_text().splitlines() if r.strip()]
for q in (4,5):
    names={}; combined=nums(a.source/f'combined-{q}.tsv')
    for row in (a.source/f'sources-{q}.tsv').read_text().splitlines():
        i,s=row.split();i=int(i);assert i not in names;names[i]=s
    assert len(names)==len(combined) and set(names)=={r[0] for r in combined}
    hard={row[0] for row in nums(a.source/f'hard-{q}.txt')}
    if a.complete:assert set(names)==hard
    cache={}
    for i,L,v,h in combined:
        n=names[i]
        if n=='pure-widths-4-5-6':
            assert (i,L,h)==(41718,64,0)
            t=[(a.source/f'pure-w{w}.log').read_text().split() for w in (4,5,6)]
            assert [int(s[3]) for s in t]==[4,5,6] and all(s[-2:]==['SAT','0'] for s in t)
            assert v==sum(int(s[s.index('systems')+1]) for s in t)
        elif n=='onehot-arity-2-3-4':
            assert (i,L,h)==(27723,48,0)
            t=[json.loads(x) for x in (a.source/'onehot-relaxed.tsv').read_text().splitlines() if x.rstrip().endswith('}')]
            assert [s['arity'] for s in t]==[2,3,4] and all(s['hits']==0 for s in t) and v==sum(s['visits'] for s in t)
        else:
            if n not in cache:
                found=next((d/n for d in [a.source,a.logs] if (d/n).is_file()),None);assert found,n
                cache[n]={tuple(map(int,l.split())) for l in found.read_text().splitlines() if len(l.split())==4 and all(x.isdigit() for x in l.split())}
                if a.save:
                    a.save.mkdir(parents=True,exist_ok=True);(a.save/n).write_bytes(found.read_bytes())
            assert (i,L,v,h) in cache[n],(q,n,i)
    hits={r[0] for r in combined if r[-1]}
    if hits:
        refined=nums(a.source/f'refined-{q}.tsv')
        assert {r[0] for r in refined}==hits and all(not r[1] for r in refined)
    print(f'q={q}: {len(combined)}/{len(hard)} accounted for; {len(hits)} rechecks required')

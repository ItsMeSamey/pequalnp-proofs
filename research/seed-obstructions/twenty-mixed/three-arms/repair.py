from itertools import combinations
from pathlib import Path
from sys import argv

def run(path, remaining):
    rows=iter(Path(path).read_text().splitlines())
    n,e,m,r=map(int,next(rows).split());stars=list(map(int,next(rows).split()))
    for _ in range(m):next(rows)
    rel=[tuple(map(int,z.split())) for z in rows]
    assert len(rel)==r
    count=0
    for entry in Path(remaining).read_text().splitlines():
        *fs,basecost=map(int,entry.split());b=len(fs);size=1<<b
        x=[sum(((f>>p)&1)<<i for i,f in enumerate(fs)) for p in range(n)]
        # For each off-union point, retain every valuation still possible after
        # replaying all obligations whose raw negative contains that point.
        forb=0
        for k in range(e):
            possible=(1<<size)-1
            for p,negative,outs in rel:
                if not outs>>k&1:continue
                z=sum(bool(f&negative)<<i for i,f in enumerate(fs))
                for u in range(size):
                    if not x[p]&~(z|u):possible&=~(1<<u)
            forb|=possible
        raw=[sum(((u>>i)&1)<<u for u in range(size)) for i in range(b)]
        def cost(pool):
            total=0
            for t in stars:
                negatives=forb
                for p in range(n):
                    if not t>>p&1:negatives|=1<<x[p]
                best=3
                for gate in pool:
                    if gate&negatives:continue
                    best=min(best,sum(not(gate>>x[p]&1) for p in range(n) if t>>p&1))
                total+=best
            return total
        assert cost(raw)==basecost
        assert any(1+cost([*raw,h])<=b for a,c in combinations(raw,2) for h in (a&c,a|c))
        count+=1
    print('One-gate repairs',path,count)
if __name__=='__main__':run(argv[1],argv[2])

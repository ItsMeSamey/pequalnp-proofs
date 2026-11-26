from pathlib import Path
goal=818815
rows=[(goal>>(6*r))&63 for r in range(4)]
cols=[sum(((row>>c)&1)<<r for r,row in enumerate(rows)) for c in range(6)]
for shore in (rows,cols):
    for i,x in enumerate(shore):
        assert any(x&~y for j,y in enumerate(shore) if j!=i)
flags=[sum(1<<k for k in range(24) if k//6==i) for i in range(4)]
flags += [sum(1<<k for k in range(24) if k%6==i) for i in range(6)]
flags.append(flags[7]|flags[8]|flags[9])
lines=iter(Path('result.log').read_text().splitlines())
for n,s,found in [(9,1023,False),(7,1151,False),(10,1023,True),(8,1151,True)]:
    line=next(lines).split()
    assert line[:4]==[str(goal),str(n),str(s),'SAT' if found else 'UNSAT']
    if found:
        known={y for i,y in enumerate(flags) if s>>i&1}
        for _ in range(n):
            a,op,b,eq,y=next(lines).split()
            a,b,y=map(int,(a,b,y))
            assert eq=='=' and op in ('&','|') and a in known and b in known
            assert all(((y>>k)&1)==((((a>>k)&1) & ((b>>k)&1)) if op=='&' else (((a>>k)&1) | ((b>>k)&1))) for k in range(24))
            known.add(y)
        assert y==goal
assert list(lines)==[]
print('Ten necessary raw flags, four declared endpoints, both positive traces replayed on 24 cells')

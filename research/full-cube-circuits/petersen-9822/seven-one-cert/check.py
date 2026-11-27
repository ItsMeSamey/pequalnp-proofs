import json
from pathlib import Path
g = json.loads(Path(__file__).with_name('upper19-seven.json').read_text())
F=(1<<128)-1
use=[[] for _ in range(10+len(g))]; use[-1]=[F]
branches=set();j=0;njoins=0;raw=[0]*10;act=[]
for i in reversed(range(len(use))):
    assert use[i]
    m=0
    for h in use[i]:m|=h
    njoins+=len(use[i])-1
    if i<10:raw[i]=m;continue
    op,a,b=g[i-10]
    if op=='or':use[a].append(m);use[b].append(m);continue
    H=sum(1<<p for p in range(128) if p>>j&1)
    branches.update([m&H,m&~H])
    act.append(m);use[a].append(m&~H);use[b].append(m&H);j+=1
mis=[50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773]
for I in mis:
    room=F
    for v,r in enumerate(raw):room &= (~r if I>>v&1 else r)
    assert room
assert njoins==10 and j==7
print('paid joins',njoins,'direct',sum(r in branches for r in raw),'full',act.count(F),'MIS',len(mis))

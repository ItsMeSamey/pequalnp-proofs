"""Run one bounded, foreground slice using an independent driver, under the workspace lock."""
from independent import ledger,src
from high_one_nonempty import solve
from itertools import combinations
import sys,time,datetime,hashlib
label,start,n=map(int,sys.argv[1:])
table=ledger()
for j in range(start,start+n):
    t,b,z=table[label][j]
    tick=time.monotonic(); kept=[]
    for size in (0,1,2):
        for group in combinations(range(7),size):
            f=sum(1<<i for i in group)
            for r in solve(b,z,f,1<<t):kept.append((f,r))
    stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
    print(stamp,t,j,b,z,len(kept),round(time.monotonic()-tick,5),hashlib.sha256(repr((t,j,b,z,kept)).encode()).hexdigest(),flush=True)
    assert not kept,(t,b,z,kept)

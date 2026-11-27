"""Independent physical-assignment controls for two automatic discovery APIs."""
import os,fcntl,hashlib,itertools,json,resource,signal
from pathlib import Path
lk='/workspace/scratch/pnp-native-search.lock'
handle=open(lk,'a')
def inode(s): return (s.st_dev,s.st_ino)
key=inode(os.fstat(handle.fileno()))
assert key==inode(os.stat(lk))
fcntl.flock(handle,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert key==inode(os.stat(lk))
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.025,.025)
import observation_block_network as net
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(net.__file__)=='2df08ff99b1d8e032b2785fb1b6804ede33d492d1894c2985bbcf4692693b144'
def sat(rows,w):
    return all(any(((w>>(abs(x)-1))&1)==int(x>0) for x in row) for row in rows)
def exhaustive(n,rows,ids,blocks):
    c=net.compile(n,rows,ids,blocks,incidence_cap=200)
    groups={}
    for w in range(1<<n):
        if sat(rows,w):
            k=sum(((w>>(v-1))&1)<<j for j,v in enumerate(ids))
            groups.setdefault(k,set()).add(w)
    ports=[p for edge in c.wires for p in edge]
    assert sorted(ports)==sorted((i,j) for i,s in enumerate(c.scopes) for j in range(len(s)))
    for (a,j),(b,k) in c.wires: assert c.scopes[a][j]==c.scopes[b][k]
    for k in range(1<<len(ids)):
        assert c.observed(k)==(k in groups)
        w=c.lift(k)
        if k in groups: assert w in groups[k] and c.fiber==len(groups[k])
        else: assert w is None
    return c,len(groups)
ids=(6,3,9,1,7,5,2,8,4)
blocks=[tuple(3*i+j for j in range(3)) for i in range(3)]+[tuple(3*j+i for j in range(3)) for i in range(3)]
offset=0b101110001
rows=[]
for s in blocks:
    rhs=sum((offset>>j)&1 for j in s)%2
    for w in range(8):
        if w.bit_count()%2!=rhs: rows.append(tuple(-ids[j] if w>>t&1 else ids[j] for t,j in enumerate(s)))
rows.extend([(ids[0],-ids[4],ids[8]),(-ids[1],ids[6])])
c,mass=exhaustive(11,rows,ids,blocks)
assert c.rank==4 and c.fiber==4
assert net.compile(11,rows,ids,blocks[:3],incidence_cap=200) is None
assert net.compile(11,rows,ids,blocks,incidence_cap=2) is None
tiny,count=exhaustive(4,[(1,),(-1,2,3)],(3,1,2,4),[(1,)])
assert len(tiny.wires)<=16
# Direct sum over each independently assigned wire, with no shared-word shortcut.
contract=0
for w in range(1<<len(tiny.wires)):
    local=[0]*len(tiny.scopes)
    for e,ends in enumerate(tiny.wires):
        if w>>e&1:
            for i,j in ends: local[i]|=1<<j
    contract+=all(tiny.entry(i,v) for i,v in enumerate(local))
assert contract==count
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(net.__file__),large_observations=mass,tiny_contraction=contract,tiny_edges=len(tiny.wires),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

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
import boundary_scalar_iter as backend, observation_block_network as net
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(backend.__file__)=='df586d60a7be61f98e6858bd0491fc1076168f50b332170f75321810dd1760ae'
assert sha(net.__file__)=='2df08ff99b1d8e032b2785fb1b6804ede33d492d1894c2985bbcf4692693b144'
def sat(rows,w):
    return all(any(((w>>(abs(x)-1))&1)==int(x>0) for x in row) for row in rows)
def sols(n,eqs,rows):
    return [w for w in range(1<<n) if all((h&w).bit_count()%2==v for h,v in eqs) and sat(rows,w)]
rec=[]
for offsets in itertools.product((0,1),repeat=2):
    a,b=offsets
    eqs=[(3,a),(5,b),(6,a^b),(3,a)]
    for signs in itertools.product((1,-1),repeat=3):
        x,y,z=signs
        rows=[(x,2*y,3*z),(2,-4),(-1,5),(3,4,-5)]
        expected=sols(7,eqs,rows)
        for tree in [((0,1),(2,3)),((3,1),(0,2))]:
            out=backend.scalar(7,eqs,rows,tree=tree,budget=10000)
            assert out['status']=='exact' and out['count']==len(expected)
            assert out['witness'] in expected if expected else out['witness'] is None
        rec.append(len(expected))
for eqs,rows in [([],[]),([],[()]),([(0,1)],[])]:
    r=backend.scalar(3,eqs,rows,budget=10000)
    assert r['count']==len(sols(3,eqs,rows))
eqs,rows=[(3,1)],[(1,3),(2,4)]
assert backend.scalar(5,eqs,rows,budget=0)['status']=='budget'
calls=[]
def fallback(d,e,c):
    calls.append(d)
    m=sols(d,e,c)
    return len(m),m[-1]
r=backend.scalar(5,eqs,rows,budget=0,fallback=fallback)
assert calls==[5] and r['status']=='fallback' and r['witness']==sols(5,eqs,rows)[-1]
ids=(6,3,9,1,7,5,2,8,4)
blocks=[tuple(3*i+j for j in range(3)) for i in range(3)]+[tuple(3*j+i for j in range(3)) for i in range(3)]
offset=0b101110001
rows=[]
for group in blocks:
    rhs=sum((offset>>j)&1 for j in group)%2
    for w in range(8):
        if w.bit_count()%2!=rhs:
            rows.append(tuple(-ids[j] if w>>i&1 else ids[j] for i,j in enumerate(group)))
rows.extend([(ids[0],-ids[4],ids[8]),(-ids[1],ids[6])])
chart=net.compile(11,rows,ids,blocks,incidence_cap=200)
expected=sols(11,[],rows)
r=backend.network(chart,budget=100000)
assert r['status']=='exact' and r['count']==len(expected) and r['witness'] in expected
assert r['network_count']*4==len(expected)
local=[0]*len(chart.atoms)
for j,ends in enumerate(chart.wires):
    if (r['wire_witness']>>j)&1:
        for v,i in ends: local[v]|=1<<i
assert all(chart.entry(i,w) for i,w in enumerate(local))
deep=0
for j in range(1,2000): deep=(deep,j)
long_rows=[(1,)]*2000
s=backend.scalar(4,[],long_rows,tree=deep,budget=1000000)
assert s['status']=='exact' and s['count']==8 and sat(long_rows,s['witness'])
s=backend.scalar(4,[],long_rows,tree=deep,budget=0,fallback=fallback)
assert s['status']=='fallback' and s['count']==8
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(backend.__file__),crossed_tree_scores=2*len(rec),skew_depth=1999,raw_count=r['count'],network_count=r['network_count'],wire_count=len(chart.wires),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

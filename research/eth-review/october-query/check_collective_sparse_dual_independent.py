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
import collective_sparse_dual as dual
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(dual.__file__)=='4b785c581f7599c0554349d9fb49da5f96840a386bdd5e36d261780bab06869d'
def sat(rows,w):
    return all(any(((w>>(abs(x)-1))&1)==int(x>0) for x in row) for row in rows)
def parity(w): return w.bit_count()%2
directions=(1,2,4,3,6,7,5)
def recode(a,bs):
    v=0
    for i,b in enumerate(bs):
        if a>>i&1: v^=b
    return v
bases=0
for bs in itertools.permutations(range(1,8),3):
    cols=[recode(a,bs) for a in directions]
    if len(set(cols))!=7: continue
    assert all(sum((c>>i)&1 for c in cols)==4 for i in range(3))
    assert max(c.bit_count() for c in cols)==3
    assert all(cols[i]^cols[(i+1)%7]!=cols[(i+2)%7] for i in range(7))
    bases+=1
assert bases==168
def fixture(offset):
    rows=[]
    for i,d in enumerate(directions):
        # Apply an invertible nonsystematic basis change before assigning gates.
        d=recode(d,(3,5,7))
        ids=[j+1 for j in range(3) if d>>j&1]+[4+i]
        rows.extend(tuple(-v if x>>j&1 else v for j,v in enumerate(ids)) for x in range(1<<len(ids)) if parity(x)!=(offset>>i&1))
    rows.extend((-(4+i),4+(i+1)%7,4+(i+2)%7) for i in range(7))
    return tuple(rows)
args=dict(order=3,probe_cap=100,clause_cap=50)
counts=[]
for offset in (0,0b1010110,127):
    rows=fixture(offset)
    chart=dual.compile(11,rows,**args)
    assert len(chart.observables)==7 and chart.rank==3 and len(chart.checks)==4 and chart.fiber==2
    assert all(h.bit_count()==3 for h,b in chart.checks)
    raw=[x for x in range(2048) if sat(rows,x)]
    by={}
    for x in raw:
        y=sum(((x>>(v-1))&1)<<i for i,v in enumerate(chart.observables))
        by.setdefault(y,set()).add(x)
    for y in range(128):
        assert sat(chart.clauses,y)==(y in by)
        w=chart.lift(y)
        if y in by: assert len(by[y])==2 and w in by[y]
        else: assert w is None
    for k,v in [('order',2),('probe_cap',2),('clause_cap',3)]:
        capped=dict(args,**{k:v})
        assert dual.compile(11,rows,**capped) is None
    for order,route in [(2,'original'),(3,'chart')]:
        actual=dual.solve(11,rows,**dict(args,order=order))
        assert actual['route']==route and actual['count']==len(raw)
        assert actual['witness'] in raw if raw else actual['witness'] is None
    counts.append(len(raw))
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(dual.__file__),bases=bases,counts=counts,compact_words=384,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

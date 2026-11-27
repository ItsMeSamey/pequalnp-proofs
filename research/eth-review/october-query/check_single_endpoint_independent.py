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
import single_endpoint_cnf as ep
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(ep.__file__)=='218c82bdbc06d0ca122563ae8e082a7800e36170f5722eb7dc6a4ca76325a935'
cases=[]
for clauses in [[(1,-2,3),(-1,2,-3)],[(1,-2,3),(-1,),(2,),(-3,)]]:
    sols=[w for w in range(8) if all(any(((w>>(abs(v)-1))&1)==(v>0) for v in c) for c in clauses)]
    for p in (1,4):
        result,coef,counts,D=ep.count(clauses,3,4,p)
        assert D==84 and len(coef)==12+p and result==sum(coef)%(1<<p)==len(sols)%(1<<p)
        assert counts['physical_copy_assignments']==64
        cases.append([p,len(sols),result,len(coef)])
rows=((1,2,-3),(1,-4,5))
for p in (1,5):
    val,cs,_,_=ep.count(rows,5,4,p)
    raw=sum(all(any(((w>>(abs(v)-1))&1)==(v>0) for v in c) for c in rows) for w in range(32))
    assert raw==25 and val==raw%(1<<p)
    cases.append([p,raw,val,len(cs)])
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(ep.__file__),cases=cases,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

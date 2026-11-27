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
import math, random
import normalized_affine_digits as solver
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(solver.__file__)=='59aa85f9b553a84911f8625e6a1cb718bd95b09b1243fe210fa54f62e7ced357'
rng=random.Random(872)
cases=0
for f,r in itertools.product(range(5),repeat=2):
    for h in range(2):
        rows=[[rng.randrange(-19,20) for j in range(f+1)] for i in range(r)]
        S=(1<<r)*sum(math.prod(a[0]+sum(v*b for v,b in zip(a[1:],x)) for a in rows) for x in itertools.product((0,1),repeat=f))
        q,rem=divmod(S,1<<max(f,r))
        assert rem==0
        for k in range(1,5):
            assert solver.normalized_product(rows,f,k)==q%(1<<k)
            cases+=1
def hm(matrix,left):
    if not left: return 1
    a,*xs=left
    return sum(matrix[a][b]*hm(matrix,tuple(c for c in xs if c!=b)) for b in xs)
mats=0
for n,mode in itertools.product((0,2,4,6,8),range(3)):
    a=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i):
            w=0 if mode==0 else rng.randrange(-9,10)*mode
            a[i][j]=a[j][i]=w
    want=hm(a,tuple(range(n)))
    for k in range(1,5):
        assert solver.hafnian(a,k)==want%(1<<k)
        mats+=1
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(solver.__file__),products=cases,hafnians=mats,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

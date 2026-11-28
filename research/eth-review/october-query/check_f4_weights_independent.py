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
import check_weighted_endpoint_paths as producer
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(producer.__file__)=='2c5a193272d2eaf22bbca4404242b4098cab6c0377b5a04548e249f111a172d1'
def mul(a,b):
    w=(a if b&1 else 0)^((a<<1) if b&2 else 0)
    return w^7 if w&4 else w
fixtures=[(((-1,-2),),((2,3),)),(((-1,),(-2,)),((3,),(2,))),(((1,),(-1,)),((1,),(2,)))]
cases=0
for rows,paths in fixtures:
    k=max(abs(v) for row in rows for v in row)
    sols=[w for w in range(1<<k) if all(any((w>>(abs(v)-1)&1)==(v>0) for v in row) for row in rows)]
    polys=[producer.tables(rows,paths,b) for b in range(2)]
    for weight in itertools.product(range(4),repeat=k):
        want=0
        for w in sols:
            a=1
            for i,x in enumerate(weight):
                if w>>i&1:a=mul(a,x)
            want^=a
        p,q=[producer.weighted(ps,weight) for ps in polys]
        assert p[0]==want
        # Horner in the formal polynomial ring, independently implementing shift by 1.
        norm=[]
        for coeff in reversed(p):
            norm=[x^y for x,y in itertools.zip_longest(norm,[0]+norm,fillvalue=0)]
            norm[0]^=coeff
        assert norm[:len(q)]==q and not any(norm[len(q):])
        cases+=1
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(producer.__file__),weight_cases=cases,raw_model_counts=[3,1,0],rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

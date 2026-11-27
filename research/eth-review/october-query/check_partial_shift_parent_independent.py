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
import math
from fractions import Fraction
import partial_shift_affine as backend
from packet_entry_tape import Ring
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(backend.__file__)=='37bc2c87ce5e3e001c89c55d40b3a801719d6de8a3a79d04a94940a395ddeba5'
def ref(edges,pks,p,z,par,sign):
    mod=1<<p
    e=len(edges)
    L=len(pks[0])
    kernel={}
    for d in range(1-L,L):
        frac=Fraction(math.prod(1+2*L*z-q for q in range(-L,L) if q!=d), math.prod(-q for q in range(-L,L) if q))
        kernel[d]=frac.numerator*pow(frac.denominator,-1,mod)%mod
    orders=[0]*(2*e+1)
    direct=0
    for X in range(1<<e):
        for Y in range(1<<(2*e)):
            if any(sum((Y>>(2*j+b))&1 for j,edge in enumerate(edges) for b,v in enumerate(edge) if v==vertex)%2!=par.get(vertex,0) for vertex in set(v for edge in edges for v in edge)): continue
            phase=(-1)**((sign&(Y|(X<<(2*e)))).bit_count()%2)
            total=phase
            poly=[phase]
            for pk in pks:
                for i,row in enumerate(pk):
                    if row is None: continue
                    y=(Y>>row)&1
                    native=sum(kernel[j-i]*((X>>(col//2))&1) for j,col in enumerate(pk) if col is not None)
                    native=native if y else 1-native
                    c=pk[i+1] if i+1<L else None
                    shifted=0 if c is None else (X>>(c//2))&1
                    base=int(shifted==y)
                    delta=native-base
                    poly=[(base*(poly[k] if k<len(poly) else 0)+delta*(poly[k-1] if k else 0))%mod for k in range(len(poly)+1)]
                    total=total*native%mod
            direct+=total
            for k,t in enumerate(poly): orders[k]+=t
    assert direct%mod==sum(orders)%mod
    return direct%mod,[v%mod for v in orders]
cases=interact=negative=0
sample=None
for edges,pks in [([(3,7),(7,3)],[(2,0,3,1)]), ([(3,7),(7,8)],[(3,None,1,None),(2,0,None,None)])]:
    for p in (2,5,9):
        r=Ring(p,(1,),1)
        for par in ({},{3:1},{7:1}):
            for sign in (0,1,18,63):
                val,orders=ref(edges,pks,p,1,par,sign)
                actual,stats=backend.evaluate(edges,pks,r,r.scalar(1),parity=par,sign=sign)
                assert actual==r.scalar(val)
                if any(orders[2:]):
                    interact+=1
                    if sample is None: sample=[p,val,orders]
                if sign: negative+=1
                cases+=1
assert interact>0 and negative>0
for bad in [[(0,0,2,3)],[(0,1,None,3)]]:
    try: backend.evaluate([(3,7),(7,3)],bad,r,r.scalar(1))
    except ValueError: pass
    else: raise AssertionError('invalid physical layout accepted')
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(backend.__file__),cases=cases,signed_cases=negative,nonzero_higher_order=interact,sample=sample,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

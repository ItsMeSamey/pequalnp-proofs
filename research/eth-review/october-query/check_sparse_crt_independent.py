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
import sparse_crt_contraction as mod
from math import prod
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(mod.__file__)=='0f2fcdeac982f92e7bfec2e32bc325a220e0f9204ce1503765a2109acf9fbef4'
calls=[]
def dense(w,vs,p,entry):
    full=sum(prod(entry(i,tuple(x>>j&1 for j in v.ports)) for i,v in enumerate(vs)) for x in range(1<<w))
    calls.append((full,p))
    return full%(1<<p)
V=mod.Vertex
lim=mod.Limits(45,64,211,200)
cases=[]
for sg in (-1,1):
    H=(1<<43)+79
    v=[V(0,(0,1),residue=lambda b,q:sg*H,abs_bound=H),V(1,(1,0),boolean=lambda b:True),V(0,(),residue=lambda b,q:-3,abs_bound=3)]
    before=len(calls)
    a,k=mod.contract(2,v,dense,lim)
    assert a==-12*sg*H and k==len(calls)-before and all(abs(a)>1<<p for _,p in calls[before:])
    cases.append(a)
    for limits in (mod.Limits(0,64,211,200),mod.Limits(45,1,211,200),mod.Limits(45,64,3,200),mod.Limits(45,64,211,8)):
        try:mod.contract(2,v,dense,limits)
        except mod.LimitExceeded:continue
        raise AssertionError('cap missed')
v=[V(0,(0,1),boolean=lambda b:b[0]!=b[1]),V(1,(1,0),boolean=lambda b:b[0] or not b[1])]
assert mod.contract(2,v,dense,lim)==(1,1)
assert mod.contract(0,[V(1,(),residue=lambda b,q:0,abs_bound=0)],dense,mod.Limits(0,0,0,0))==(0,0)
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(mod.__file__),signed_extrema=cases,backend='finite exhaustive',rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

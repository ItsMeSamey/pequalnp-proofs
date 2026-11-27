"""Independent supplied-layout controls. Execute in a coordinated native slot."""
import fcntl,hashlib,json,os,resource,signal
from fractions import Fraction
from pathlib import Path
path="/workspace/scratch/pnp-native-search.lock"
lock=open(path,"a")
def inode(st): return st.st_dev,st.st_ino
assert inode(os.stat(path))==inode(os.fstat(lock.fileno()))
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
assert inode(os.stat(path))==inode(os.fstat(lock.fileno()))
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def mem(*_): assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,mem)
signal.setitimer(signal.ITIMER_PROF,.025,.025)
import packet_polynomial_dp as dp
import signed_crossing_layout_oracle as oracle
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
assert sha(dp.__file__)=="3589f579fc36326213c6c4f308ea835507bb33b8050d7253401aaa724cae9cd5"
assert sha(oracle.__file__)=="cd877070da893aea96d4841486744463bd5f808c3644e0a220e2343ec8385a1e"
results=[]
for sat in (False,True):
    cs=oracle.clauses(sat)
    p=oracle.PACKETS
    low=dp.source(3,cs,p,work_cap=0)
    assert low["status"]=="unknown"
    fallback_calls=[]
    def fallback(n,original,slots):
        fallback_calls.append((n,original,slots))
        return {"status":"fallback_control"}
    assert dp.source(3,cs,p,work_cap=0,fallback=fallback)=={"status":"fallback_control"}
    assert fallback_calls==[(3,cs,p)]
    ans=dp.source(3,cs,p,work_cap=10**18)
    assert ans["status"]=="exact" and ans["count"]==2*int(sat)
    observations={}
    for point in (0,5):
        ref=2*oracle.reference(sat,point,p)
        got=Fraction(sum(c*point**i for i,c in enumerate(ans["numerator"])),ans["denominator"])
        assert got==ref
        observations[str(point)]=str(got)
    assert observations["5"]!="0" and observations["5"]!=observations["0"]
    results.append(dict(sat=sat,values=observations,peak=ans["max_enum_width"],
                        fallback_calls=len(fallback_calls),order=ans["packet_order"]))
for cs,expected in [((),8),(((1,-1),),8),(((3,),()),0)]:
    ans=dp.source(3,cs,(),work_cap=0)
    assert ans["status"]=="exact" and ans["numerator"]==(expected,) and ans["denominator"]==1
mem()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(harness=sha(__file__),target=sha(dp.__file__),records=results,
                      constant_cases=3,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

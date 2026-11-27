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
import automatic_packet_separator as planner
import packet_polynomial_witness as evaluator
import signed_crossing_layout_oracle as oracle
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(planner.__file__)=="f87818e4185d307b5c30ee4c18bda4be7ad13cb77f088678f18a0f1991bf6f1e"
assert sha(evaluator.__file__)=="d75a5c8a8f3742b777984d570eac1eae377a8da0a8f8b7a8184625c23c33963f"
assert sha(oracle.__file__)=="cd877070da893aea96d4841486744463bd5f808c3644e0a220e2343ec8385a1e"
params=dict(r=2,a=1,u=1,delta=3,slot_cap=128,placement_cap=1,width_cap=30,strict=False)
controls=[]
for sat in (True,False):
    raw=oracle.clauses(sat)
    ans=planner.recognize(3,raw,**params)
    assert ans["status"]=="found" and ans["strict"] is False
    pk=tuple(ans["packets"])+((None,None),)
    order=tuple(ans["packet_order"])
    result=evaluator.solve(3,raw,pk,work_cap=10**19,packet_order=order)
    assert result["status"]=="exact" and result["count"]==2*int(sat)
    assert result["witness"]==(3 if sat else None)
    p=result["numerator"]
    off=Fraction(sum(c*3**i for i,c in enumerate(p)),result["denominator"])
    assert off==2*oracle.reference(sat,3,pk)
    assert set(result["packet_order"])==set(range(len(pk)))
    if sat:
        narrow=evaluator.solve(3,raw,pk,work_cap=result["work_bound"],packet_order=order)
        assert narrow["status"]=="unknown" and narrow["reason"]=="witness_budget" and narrow["exact_count"]==2
    controls.append(dict(sat=sat,count=result["count"],witness=result["witness"],off_grid=str(off),
                         chosen_width=ans["profile"]["width"],dp_width=result["max_enum_width"]))
joint=planner.execute(3,oracle.clauses(True),work_cap=10**19,witness=True,pins=((0,1),),**params)
assert joint["status"]=="found" and joint["readout"]["count"]==2 and joint["readout"]["witness"]==3
blocked=planner.execute(3,oracle.clauses(True),work_cap=10**19,witness=True,pins=((0,0),),**params)
assert blocked["readout"]["count"]==0
narrow=planner.recognize(3,oracle.clauses(True),**dict(params,placement_cap=0,width_cap=0))
assert narrow["status"]=="unknown" and narrow["stats"]["placements"]==0
mem()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(controls=controls,work_cap_control=True,search_cap_control=True,
                      native_schedule=False,harness=sha(__file__),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

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
import reciprocal_child_machine as rec
from variable_packet_machine import shifted_kernel,solve as original
from variable_packet_machine_affine import Description,solve
from source_cnf_driver import Predicate
from packet_entry_tape import Ring
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(rec.__file__)=='8b3d5ae1f613903114fa1625dc7ce2066bdcc41fe7dc5c1e5a0b175d17cff7d3'
def source(width,sign):
    unit=Predicate('or',(sign,),3,width)
    cp=Predicate('copy',(),2,width)
    return (((unit,(0,)),(cp,(1,))),((cp,(0,1)),))
labels=([0,0],[1]);f=(1,1)
r=Ring(14,f,2);nw=source(4,0)
layout=((0,None,None,None,1,None,None,None),)
stats=[];all_keys=set();nonzero_keys=set()
for t,z in [(1,(0,1,0,1)),(-1,(1,3,1,2))]:
    pending=[]
    def visit(beta,g,child):
        assert all(isinstance(d,Description) and d.ring==r for d,es in child[1])
        pending.append((beta,g))
        all_keys.update((idx[-1],k) for idx,k in beta)
    def dense(child,m,ring):
        v=solve(child,m,ring.p,ring.f,ring.ell,0,lambda *_:None)
        beta,g=pending.pop()
        if any(v):nonzero_keys.update((idx[-1],k) for idx,k in beta)
        return v
    val,counts=rec.sample(nw,layout,labels,t,z,r,dense,visit=visit)
    raw=r.scalar(0)
    for X in (0,1):
        weights=[r.scalar(0),r.scalar(0)]
        if X:
            for j,x in enumerate((0,4)):
                for y in (0,4): weights[j]=r.add(weights[j],shifted_kernel(r,8,t,z,y-x))
        for Y0,Y1 in itertools.product((0,1),repeat=2):
            if Y0:continue
            pairs=[w if bit else r.add(r.scalar(1),r.neg(w)) for bit,w in zip((Y0,Y1),weights)]
            raw=r.add(raw,r.mul(*pairs))
    assert val==raw
    stats.append((counts,raw))
assert any(idx>=2 for idx,k in nonzero_keys)
# Full two-center Hermite reconstruction down to the signed unit's raw count.
ff=(1,1,0); nn=source(3,0);spec=(1,1,((0,None),(1,None)),[labels])
current=rec.solve_root(nn,2,4,ff,1,spec)
prior=original(nn,2,4,ff,1,0,lambda net,m,l: None if l else spec)
assert current==prior==(1,0,0)
cp=Predicate('copy',(),2,4); mix=Predicate('or',(1,0),3,4)
binary=(((mix,(0,2)),(cp,(1,)),(cp,(3,))),((cp,(0,1)),(cp,(2,3))))
rr=Ring(8,f,2);zz=(1,2,1,3);sites=(0,2,4,6)
got,extra=rec.sample(binary,((0,None,1,None,2,None,3,None),),([0,0,0],[1,1]),1,zz,rr,
    lambda c,m,birth:solve(c,m,birth.p,birth.f,birth.ell,0,lambda *_:None))
direct=rr.scalar(0)
for A,B in itertools.product((0,1),repeat=2):
    u=[]
    for x in sites:
        v=rr.scalar(0)
        for y,bit in zip(sites,(A,A,B,B)):
            if bit:v=rr.add(v,shifted_kernel(rr,8,1,zz,y-x))
        u.append(v)
    for Y in itertools.product((0,1),repeat=4):
        if not (Y[0] or not Y[2]):continue
        v=rr.scalar(1)
        for bit,w in zip(Y,u):v=rr.mul(v,w if bit else rr.add(rr.scalar(1),rr.neg(w)))
        direct=rr.add(direct,v)
assert got==direct
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(rec.__file__),samples=stats,mixed_or=[extra,got],nonzero_child_modes=sorted(nonzero_keys),origin=current,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

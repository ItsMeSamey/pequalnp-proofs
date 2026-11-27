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
import automatic_private_decision as auto, auto_piece_projection as piece
import private_projection_sat as binary, signed_cover_projection as signed
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
pins=('49c92b232cfc534bd875c4294db5e8f9eec22565ca446902c2339977dea384aa','0e29fd32ef703777ff2e7ab95bd6e604c0b01b107176f38b998c1614f6997a78','96f25455adce0412084f3716a0a893f0fc06f39d886c3956f4b916164ef84ddf','37cc4e33a052b0bfa17917e077249e40fcd344df148876164e0105915d72aeee')
assert tuple(sha(m.__file__) for m in (auto,piece,binary,signed))==pins
def sat(rows,w):
    return all(any(((w>>(abs(x)-1))&1)==int(x>0) for x in row) for row in rows)
def decision(rows,truth):
    a=auto.solve_auto(rows)
    assert a['status']==('sat' if truth else 'unsat')
    if truth:
        w=sum(1<<(i-1) for i,b in a['witness'].items() if b)
        assert sat(rows,w)
def check(n,rows):
    models={x for x in range(1<<n) if sat(rows,x)}
    decision(rows,bool(models))
    p=piece.project(n,rows,ports=1,width=2,budget=10000,protected=(1,))
    by={}
    for x in models:
        y=sum(((x>>(v-1))&1)<<i for i,v in enumerate(p.core))
        by.setdefault(y,set()).add(x)
    for y in range(1<<len(p.core)):
        w=p.lift(y)
        assert sat(p.clauses,y)==(y in by)
        if y in by: assert w in by[y]
        else: assert w is None
    return bool(models)
triples=list(itertools.product((1,-1),(2,-2),(3,-3)))
answers=[]
for mask in range(256):
    rows=[t for j,t in enumerate(triples) if (mask>>j)&1]
    rows+=[(1,-1,3)]
    if mask%3==0: rows+=[(-1,-1)]
    if mask%5==0: rows+=[(2,),(2,)]
    answers.append(check(4,rows))
assert check(3,[()]) is False
one=[(1,-2,3)]
assert auto.solve_auto(one,private_limit=0)['status']=='unknown'
assert piece.project(3,one,ports=0,width=0,budget=500).pieces==()
assert piece.project(3,one,ports=1,width=2,budget=0) is None
for opposite in (False,True):
    rows=[]
    for j in range(20):
        p,q=2+2*j,3+2*j
        u=-1 if opposite and j==19 else 1
        rows.extend((a*p,u,b*q) for a,b in itertools.product((1,-1),repeat=2))
    decision(rows,not opposite)
    pr=piece.project(41,rows,ports=1,width=2,budget=1000000)
    assert pr.pieces and len(pr.core)<=1
    witnesses=[pr.lift(w) for w in range(1<<len(pr.core))]
    assert any(w is not None for w in witnesses)==(not opposite)
    assert all(sat(rows,w) for w in witnesses if w is not None)
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),targets=pins[:2],small_sat=sum(answers),small_unsat=257-sum(answers),large_cover_lower_bound=20,large_status=['sat','unsat'],rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

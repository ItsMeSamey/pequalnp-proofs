"""Charge each parity query by evaluating its physical list on the source CNF assignments."""
from collections import Counter
from itertools import product
from pathlib import Path
import fcntl,resource,signal,time,json,hashlib
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.03,.03)
import coordinate_split_scores as proj
import coordinate_split_nonzero_scores as nz
import coordinate_split_nonzero_fast as fast
assert hashlib.sha256(Path(fast.__file__).read_bytes()).hexdigest()=="c294c268d123de260704ea44a27980b813eba7ff73255020f2bec78820f273ba"
assert hashlib.sha256(Path(nz.__file__).read_bytes()).hexdigest()=='96305e0bef630f7bdcce9295cbcdb0e5475f9c0ad6abb9790376e12901b6fd19'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(proj.__file__)=='78849662217b1975cc7e1c4b18d8c9b979c6e65487d8f00b7ac6676579c40fc6'
assert sha(Path(proj.__file__).with_name('coordinate_split_cnf.py'))=='d983b90d07a8ee9b5e9e251cf3c7080d5c60ed994dce611e0fbb7fff55b415f2'
def words(n,cnf,prefix):
    for x in range(1<<n):
        w=0
        for j,row in enumerate(cnf):
            if not any(bool(x>>(abs(l)-1)&1)==(l>0) for l in row):w|=1<<j
        if all((w&h).bit_count()%2==0 for h in prefix):yield w
def live(n,cnf,prefix,row):
    # Do not use a free lookup into an existing table of trial or Walsh scores.
    return sum(sum(c*((word>>i)&1) for i,c in row)%2==0 for word in words(n,cnf,prefix))
def mask(row):
    a=0
    for i,c in row:a^=c<<i
    return a
receipt=[]
def verify(n,cnf,prefix,L,cap,budget,status,base=None,reach=None,nonzero=False):
    m=len(cnf)
    expected=Counter(words(n,cnf,prefix))
    asked=[]
    def actual(row):
        h=mask(row)
        canonical=tuple((j,1) for j in range(m) if h>>j&1)
        canonical+=((0,0),)*(L-len(canonical)) if m else ()
        assert row==canonical and h not in asked
        asked.append(h)
        return live(n,cnf,prefix,row)
    engine=(fast.recover_nonzero if nonzero==2 else nz.recover_nonzero_prefix) if nonzero else proj.recover_prefix
    res=engine(m,L,cap,actual,max_calls=budget,base=base)
    assert res['status']==status and res['calls']==len(asked)<=budget,(res,status,asked)
    assert res['max_row_weight']==max((h.bit_count() for h in asked),default=0)
    if reach is not None:assert reach==res['max_row_weight']
    if status=='exact':
        assert res['histogram']==expected and res['count']==expected[0]
    elif status=='support_overflow':assert cap<res['certified_at_least']<=len(set(expected)-({0} if nonzero else set()))
    elif status=='row_length':assert res['required']>L
    if base is not None: assert 0 not in asked
    receipt.append((status,len(asked),res['max_row_weight']))
units=[[1],[2],[3]]
verify(4,units,[7],3,4,8,'exact',reach=3)
verify(4,units,[7],2,4,8,'row_length')
verify(4,units,[7],3,3,8,'support_overflow')
verify(4,units,[7],3,4,7,'query_cap')
verify(4,units,[7],3,4,7,'exact',base=8,reach=3)
verify(4,units,[1,2,4],1,1,4,'exact',reach=1)
verify(2,[[]],[1],0,0,1,'exact',reach=0)
verify(0,[],[],0,1,1,'exact',reach=0)
verify(4,units,[],3,4,0,'query_cap')
verify(4,units,[7],3,3,8,"exact",reach=3,nonzero=True)
verify(4,units,[7],2,3,8,"row_length",nonzero=True)
verify(4,units,[7],3,3,7,"query_cap",nonzero=True)
verify(4,units,[7],3,2,8,"support_overflow",nonzero=True)
verify(4,units,[1,2,4],1,0,4,"exact",nonzero=True)
verify(0,[],[],0,0,1,"exact",nonzero=True)
verify(2,[[]],[],1,0,2,"support_overflow",nonzero=True)
verify(2,[[]],[1],1,0,2,"exact",nonzero=True)
verify(2,[[]],[1],0,0,0,"exact",base=0,reach=0,nonzero=2)
verify(2,[[]],[1],0,0,1,"exact",reach=0,nonzero=2)
verify(4,units,[7],3,3,7,"exact",base=8,reach=3,nonzero=2)
# Genuine greedy P=3 first choice from empty, using all 8³ physical lists.
cnf=[[1,2],[1,-2],[-1,2],[3]]
rows=list(product(tuple(product(range(4),range(2))),repeat=3))
vals=[live(3,cnf,[],r) for r in rows]
winner=rows[vals.index(min(vals))]
assert mask(winner)==7
verify(3,cnf,[mask(winner)],3,2,32,'exact')
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(checker=sha(__file__),solver=sha(proj.__file__),trials=receipt,selected_first=winner,selected_min=min(vals),cpu_s=time.process_time(),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

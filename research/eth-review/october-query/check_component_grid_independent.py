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
import component_grid_band as component, all_grid_cnf_band as flat
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(component.__file__)=='65454545f0d106c25134bfa9747327ede2cef717408ab41e110b4bbafb03d82e'
def inp(kinds,s):
    cs=[];ps=[];g=[]
    for b,kind in enumerate(kinds):
        for i in range(s):
            n=b*s+i
            neg=(kind!='free' and (i==0 or (kind=='det' and i==1)))
            cs.append((-(n+1) if neg else n+1,))
            g+=[('or',(2*n,),int(neg)),('copy',(2*n+1,),None)]
        ps.append(tuple(2*s*b+(i^int(kind=='free')) for i in range(2*s)))
    return cs,ps,g
large=[]
for kind,want in [('det',7),('free',21)]:
    cs,ps,_=inp(['tie']*7+[kind],8)
    a=component.supplied(64,cs,ps,center=15,excess=0,digits=5,word_cap=4)
    assert a['values']==(want,) and a['components']==8 and a['cache_hits']==6 and a['spent_words']==4
    assert component.supplied(64,cs,ps,center=15,excess=0,digits=5,word_cap=3)['status']=='unknown'
    large.append(a['values'][0])
cs,ps,gs=inp(['det','free'],2)
small=[]
for t in (-3,0,3):
    ref=flat.evaluate(gs,ps,center=t,excess=2,digits=3)
    for cutoff in (-1,8):
        a=component.supplied(4,cs,ps,center=t,excess=2,digits=3,cube_bits=cutoff)
        assert a['values']==ref['values']
    small.append(ref['values'])
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(component.__file__),five_bit=large,three_order_band=small,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

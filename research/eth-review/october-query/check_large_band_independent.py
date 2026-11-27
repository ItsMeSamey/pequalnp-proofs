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
import extreme_cnf_band as band, normalized_affine_digits as core
from math import prod
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(band.__file__)=='cdf97776e0bb58ce6abee67174b4e5295acfcbba386cbdcff490fcdeba1852cf'
assert sha(core.__file__)=='59aa85f9b553a84911f8625e6a1cb718bd95b09b1243fe210fa54f62e7ced357'
def make(kind,s):
    gs=[]
    for i in range(s):
        neg=(kind!='free' and (i==0 or (kind=='det' and i==1)))
        gs.extend([('or',(2*i,),int(neg)),('copy',(2*i+1,),None)])
    p=tuple(i^int(kind=='free') for i in range(2*s))
    return gs,p
def value(kind,s):
    gs,p=make(kind,s)
    L=2*s
    succ,live,reads=band._layout([p],L-1,L)
    dormant=[k=='or' and w==0 and succ.isdisjoint(ps) for k,ps,w in gs]
    r=sum(dormant)
    f=s-len(live)
    debt=max(0,f-r)
    bits=5+debt
    mod=1<<bits
    K=band._kernels(L,L-1,2,bits)
    acc=0
    for a in range(1<<s):
        rows=band._rows(reads,K,{i:i for i in range(s)},{},a,2,mod)
        coeff=[band._gate_series(k,ps,w,rows,2,mod)[int(d)].get(0,0) for (k,ps,w),d in zip(gs,dormant)]
        acc+=prod(coeff)%mod
    assert acc%(1<<debt)==0
    return (acc>>debt)%32,r,f
for kind in ('det','tie','free'):
    gs,p=make(kind,2)
    a=band.evaluate(gs,[p],center=3,excess=0,digits=5)
    assert a['values'][0]==value(kind,2)[0]
local={k:value(k,8) for k in ('tie','det','free')}
checks=[]
for special,want in [('det',7),('free',21)]:
    blocks=['tie']*7+[special]
    gs=[]
    ps=[]
    for b,k in enumerate(blocks):
        g,p=make(k,8)
        gs.extend((typ,tuple(i+16*b for i in ports),w) for typ,ports,w in g)
        ps.append(tuple(i+16*b for i in p))
    result=band.evaluate(gs,ps,center=15,excess=0,digits=5,word_cap=255)
    assert result['status']=='unknown' and result['word_bound']==256
    order=sum(local[k][1] for k in blocks)
    f=sum(local[k][2] for k in blocks)
    assert order==result['order'] and f==result['outside_bits']
    delta=sum(max(local[k][1:]) for k in blocks)-max(order,f)
    obtained=prod(local[k][0] for k in blocks)*(1<<delta)%32
    assert obtained==want
    checks.append([order,f,obtained])
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(band.__file__),component_kernel_results=checks,full_dispatch='declined at 255 of 256 words',small_public_calls=3,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

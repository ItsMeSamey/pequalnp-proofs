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
import two_sided_cauchy_modes as cm
from variable_packet_machine import shifted_kernel
from packet_entry_tape import Ring
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(cm.__file__)=='7f35367452323490948d6fff1ea15e0cd1994665fc77b114f5c928c51edf81ae'
r=Ring(12,(1,1),2);one=r.scalar(1);zero=r.scalar(0)
def sc(a,k):return tuple(v*k%4096 for v in a)
def inv(v):
    x=one
    for k in range(4): x=r.mul(x,r.add(r.scalar(2),r.neg(r.mul(v,x))))
    assert r.mul(v,x)==one
    return x
kw=dict(one=one,add=r.add,mul=r.mul,scale=sc,inverse_unit=inv)
real=(0,1,2,3,4,6);pairs=((0,4),(1,3),(2,6))
high=compare=0;totals=[]
for z in [zero,(3,2,1,4)]:
    weight,cross=cm.native_entries(8,-1,z,r.p,**kw)
    W={(x,y):shifted_kernel(r,8,-1,z,y-x) for x in real for y in range(8)}
    assert all(weight(x,y)==w for (x,y),w in W.items())
    total=zero
    for X in itertools.product((0,1),repeat=3):
        bits={y:b for pair,b in zip(pairs,X) for y in pair};values={}
        for x in real:
            y0=x%2
            K,A=cross(x,y0)
            assert K==W[x,y0] and A==sc(inv(r.add(r.scalar(-1-y0+x),sc(z,16))),2)
            tile=[((y-y0)//2,bits[y]) for y in real if y%2==y0]
            sep=cm.row_tile_sum(K,A,tile,r.p,zero=zero,**kw)
            geometric=native=zero
            for y in real:
                if y%2!=y0 or not bits[y]:continue
                native=r.add(native,W[x,y]);j=(y-y0)//2
                for k in range(r.p): geometric=r.add(geometric,sc(r.mul(K,r.power(A,k)),j**k))
            assert sep==geometric==native
            high+=sum(k>=2 and any(v) for k,v in cm.target_modes(K,A,max(j for j,b in tile)+1,r.p,**kw))
            for y in real:
                if y%2!=y0 and bits[y]:sep=r.add(sep,W[x,y])
            values[x]=sep;compare+=1
        for Y in itertools.product((0,1),repeat=6):
            if not (Y[0] or not Y[1]) or not (Y[2]==Y[3]==Y[4]) or not Y[5]:continue
            term=one
            for x,b in zip(real,Y):
                v=values[x];term=r.mul(term,v if b else r.add(one,r.neg(v)))
            total=r.add(total,term)
    totals.append(total)
assert high and cm.row_tile_sum(one,zero,[],r.p,zero=zero,**kw)==zero
assert cm.mode_weight(2)==5 and cm.mode_weight(4)==11
assert all(k<2 for k,v in cm.target_modes(K,A,4,5,**kw)) and cm.column_mode(2,2,5)%2==1
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(cm.__file__),row_comparisons=compare,nonzero_high_modes=high,signed_copy_sums=totals,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

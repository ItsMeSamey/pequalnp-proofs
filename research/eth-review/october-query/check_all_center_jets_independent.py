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
from functools import lru_cache
from packet_entry_tape import Ring
import all_center_packet_jets as basejets
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pmul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c
def padd(a,b):
    return [x+y for x,y in itertools.zip_longest(a,b,fillvalue=0)]
@lru_cache(None)
def kernel(L,t,d):
    c=[1]
    for q in range(-L,L):
        if q!=d: c=pmul(c,[t-q,2*L])
    den=math.prod(-q for q in range(-L,L) if q)
    return [Fraction(x,den) for x in c]
def full(edges,pkts,t,sign,par,gate):
    e=len(edges)
    L=len(pkts[0])
    inc={}
    for j,edge in enumerate(edges):
        for i,v in enumerate(edge): inc.setdefault(v,[]).append(2*j+i)
    total=[]
    for x in range(1<<e):
        source={}
        for pk in pkts:
            for i,row in enumerate(pk):
                if row is None: continue
                v=[0]
                for j,col in enumerate(pk):
                    if col is not None and (x>>(col//2))&1: v=padd(v,kernel(L,t,j-i))
                source[row]=v
        for y in range(1<<(2*e)):
            local={v:sum(((y>>j)&1)<<i for i,j in enumerate(ps)) for v,ps in inc.items()}
            if any(bits.bit_count()%2!=par.get(v,0) for v,bits in local.items() if gate is None or v!=gate[0]): continue
            if gate and local[gate[0]]==gate[1]: continue
            p=[(-1)**(((y|(x<<(2*e)))&sign).bit_count()%2)]
            for row,a in source.items():
                p=pmul(p,a if (y>>row)&1 else padd([1],[-v for v in a]))
            total=padd(total,p)
    return total
def hasse(poly,r,z,J):
    out=[]
    for j in range(J):
        v=r.scalar(0)
        for k in reversed(range(j,len(poly))):
            a=Fraction(poly[k])*math.comb(k,j)
            v=r.add(r.mul(v,z),r.scalar(a.numerator*pow(a.denominator,-1,1<<r.p)))
        out.append(v)
    return tuple(out)
assert sha(basejets.__file__)=='6695a0bb51b31d042215a06b07e0ff4b63a67f7ee24588af4125fcb13d01d6c5'
edges=((7,4),)
pkts=((1,None,0,None),)
r=Ring(10,(1,1),2)
z=(3,2,1,5)
mixed=[]
for t in range(-4,4):
    for sign,par in [(1,{7:1}),(6,{4:1}),(0,{})]:
        poly=full(edges,pkts,t,sign,par,None)
        actual,stats=basejets.evaluate(edges,pkts,r,z,center=t,J=4,parity=par,sign=sign)
        assert actual==hasse(poly,r,z,4)
        if any(any(v[2:]) for v in actual[1:]): mixed.append((t,sign))
assert mixed
assert basejets.evaluate(edges,pkts,r,z,center=-4,J=4,term_cap=0) is None
native,stats=basejets.native(edges,pkts,(1,1),2,3,1,-1,sign=6,parity={4:1})
hi=Ring(stats['precision'],(1,1),2)
assert native==hasse(full(edges,pkts,-1,6,{4:1},None),hi,hi.scalar(0),len(native))
import signed_or_packet_jets as orgate
assert sha(orgate.__file__)=='4e95eb81b525f06d1a0424bce8a67aab17574eef8016962504c97b4d33b81ffa'
edges2=((9,4),(4,9))
p2=((1,2,None,3),(None,0,None,None))
or_cases=0
for t in (-4,-2,0,3):
    for false in (0,1,2,3):
        gate=(4,false)
        par={9:1}
        ans,st=orgate.evaluate_or(edges2,p2,r,z,center=t,J=3,vertex=4,false_word=false,parity=par,sign=17)
        assert ans==hasse(full(edges2,p2,t,17,par,gate),r,z,3)
        or_cases+=1
assert orgate.evaluate_or(edges2,p2,r,z,center=-2,J=2,vertex=4,false_word=1,term_cap=0) is None
# Encode a birth-3 signed factor with canonical coefficients 1 and 7.
# Its Fourier coefficients are (4,-3), which are ordinary integers.
t=-2
par={9:1}
one=basejets.evaluate(edges2,p2,r,z,center=t,J=3,parity=par)[0]
character=basejets.evaluate(edges2,p2,r,z,center=t,J=3,parity=par,sign=17)[0]
lifted=tuple(r.add(r.mul(r.scalar(4),a),r.mul(r.scalar(-3),b)) for a,b in zip(one,character))
ref=padd([4*x for x in full(edges2,p2,t,0,par,None)],[-3*x for x in full(edges2,p2,t,17,par,None)])
assert lifted==hasse(ref,r,z,3) and lifted!=character
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),targets=[sha(m.__file__) for m in (basejets,orgate)],parity_cases=24,or_cases=or_cases,mixed_VZ=len(mixed),native_precision=hi.p,native_J=len(native),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

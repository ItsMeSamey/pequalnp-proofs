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
                p=pmul(p,(a if (y>>row)&1 else padd([1],[-v for v in a]))[:4])[:4]
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
import center_jet_fourier as impl
def go(edges,pks,t,par,sign,J,p):
    v=sorted(set(itertools.chain.from_iterable(edges)))
    scalar=Ring(p,(0,),1)
    ref=tuple(x[0] for x in hasse(full(edges,pks,t,sign,par,None),scalar,scalar.scalar(0),J))
    w=[]
    for seq in (v,list(reversed(v))):
        value,stats=impl.evaluate(edges,pks,center=t,count=J,precision=p,order=seq,parity=par,sign=sign)
        assert value==ref
        if stats['width']:
            assert impl.evaluate(edges,pks,center=t,count=J,precision=p,order=seq,width_cap=stats['width']-1) is None
        assert impl.evaluate(edges,pks,center=t,count=J,precision=p,order=seq,term_cap=0) is None
        w.append(stats['width'])
    return w
assert sha(impl.__file__)=='c2d3e1ff0787fe8ab88f426906d6be1d0eb0664cbd5c80cf3a5babd18a04cd28'
widths=[]
for layout in [((2,0),(3,1)),((3,None,2,0),(None,1,None,None))]:
    L=len(layout[0])
    for t in range(-L,L):
        widths.extend(go([(4,7),(7,9)],layout,t,{4:1},17,1+((t+L)%4),76))
for t in (-1,0,1):
    widths.extend(go([(7,4),(4,9),(9,7)],((5,1),(2,4),(3,0)),t,{7:1},37,4,101))
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(impl.__file__),order_comparisons=len(widths),widths=sorted(set(widths)),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

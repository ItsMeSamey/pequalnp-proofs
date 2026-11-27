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
import endpoint_cover_jets as ep
assert sha(ep.__file__)=='244e9f7f6e2027c3d1fdd7ee19899f42b55086cb84c70dfb99961952021ccee8'
def contraction(gates,pks,t,J):
    L=len(pks[0])
    edges=sum(j is not None for p in pks for j in p)//2
    total=[]
    for X in range(1<<edges):
        a={}
        for pk in pks:
            for i,row in enumerate(pk):
                if row is None: continue
                a[row]=[0]
                for j,col in enumerate(pk):
                    if col is not None and (X>>(col//2))&1:
                        a[row]=padd(a[row],kernel(L,t,j-i)[:J])
        v=[1]
        for typ,ps,ss in gates:
            g=[0]
            for assignment in range(1<<len(ps)):
                bits=[(assignment>>j)&1 for j in range(len(ps))]
                if typ=='or' and not any(x==y for x,y in zip(bits,ss)): continue
                if typ=='copy' and len(set(bits))>1: continue
                q=[1]
                for i,b in zip(ps,bits):
                    row=a[i] if b else padd([1],[-j for j in a[i]])
                    q=pmul(q,row)[:J]
                g=padd(g,q)
            v=pmul(v,g)[:J]
        total=padd(total,v)
    return total
rows=[(1,-2),(-1,2)]
gates,unused,const=ep.source_rows(3,rows)
assert unused==1 and const is None
r=Ring(3+8*24*4+8*8*3,(1,),1)
cases=nonzero=0
for layout in [((3,7,0,4),(1,5,6,2)),((None,2,6,None),(0,1,5,7),(3,None,4,None))]:
    for t in range(-4,4):
        answer=ep.source_jet(3,rows,layout,r,center=t,order=2,work_cap=100000000)
        ref=hasse([2*v for v in contraction(gates,layout,t,3)],r,r.scalar(0),3)
        assert answer is not None and answer[0]==ref
        if t==0: assert ref[0]==r.scalar(4)
        if any(x[0] for x in ref[1:]): nonzero+=1
        cases+=1
assert nonzero
for rows,count in [([],8),([()],0),([(1,-1)],8)]:
    assert ep.source_jet(3,rows,(),r,center=-4,order=2,work_cap=0)[0]==(r.scalar(count),r.scalar(0),r.scalar(0))
assert ep.evaluate(gates,layout,r,center=0,order=2,work_cap=0) is None
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(ep.__file__),cases=cases,nonzero_derivatives=nonzero,precision=r.p,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

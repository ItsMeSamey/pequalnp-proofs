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
import extreme_cnf_digit as digit
assert sha(digit.__file__)=='decc3e8416bdc29e18ca5292b4efc7f6c8a6539e1e799694e7d8d7a6afadebf0'
coverage=set()
cases=0
for clauses in [((1,),(2,)),((-1,),(2,)),((-1,-2),),((1,1),),((1,),(-1,))]:
    gates=[]
    vr={}
    e=0
    for row in clauses:
        ps=[]
        for lit in row:
            ps.append(2*e)
            vr.setdefault(abs(lit),[]).append(2*e+1)
            e+=1
        gates.append(('or',ps,[int(l>0) for l in row]))
    gates.extend(('copy',ps,()) for ps in vr.values())
    unused=3-len(vr)
    for seq in [(0,1,2,3),(0,2,1,3),(1,2,0,3),(2,0,3,1)]:
        for layout in [(seq,),((seq[0],None,None,seq[1]),(None,seq[2],seq[3],None)),((seq[0],seq[1]),(seq[2],seq[3]))]:
            for t in (1-len(layout[0]),len(layout[0])-1):
                a=digit.from_clauses(3,clauses,layout,center=t)
                j=a['order']
                poly=contraction(gates,layout,t,j+1)
                v=Fraction(poly[j] if len(poly)>j else 0)*(1<<unused)
                bit=a['first_bit_position']
                value=(v.numerator*pow(v.denominator,-1,2<<bit))%(2<<bit)
                assert value==a['bit']<<bit
                cap=digit.from_clauses(3,clauses,layout,center=t,word_cap=0)
                coverage.update([('regime',a['outside_bits']>=j),('bit',a['bit']),('cap',cap['status'])])
                cases+=1
assert len(coverage)==6
growing=[]
for nunit in (0,1,2,3,4):
    rows=[(i+1,) for i in range(nunit)]
    layout=tuple((i,None) for i in range(2*nunit)) or ((None,None),)
    gs=[('or',[2*i],(1,)) for i in range(nunit)]+[('copy',[2*i+1],()) for i in range(nunit)]
    a=digit.from_clauses(nunit+1,rows,layout,center=1)
    assert a['order']==nunit and a['unused_bits']==1
    j=a['order']
    cs=contraction(gs,layout,1,j+1)
    v=2*Fraction(cs[j] if len(cs)>j else 0)
    pos=a['first_bit_position']
    assert (v.numerator*pow(v.denominator,-1,2<<pos))%(2<<pos)==(a['bit']<<pos)
    growing.append(j)
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(digit.__file__),cases=cases,extra_orders=growing,coverage=sorted(coverage,key=str),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

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
import random
import rs_coset_entries as rs
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(rs.__file__)=='b4a28282762eb013faed3d2d24557f089b301019c19e8b46f75995599b51c07e'
def mul(a,b,mod):
    val=0
    for j in range(b.bit_length()):
        if b>>j&1: val^=a<<j
    while val.bit_length()>=mod.bit_length():
        val^=mod<<(val.bit_length()-mod.bit_length())
    return val
def xor(values):
    v=0
    for u in values: v^=u
    return v
def polyprod(f,g,m):
    return [xor(mul(f[i],g[k-i],m) for i in range(len(f)) if 0<=k-i<len(g)) for k in range(len(f)+len(g)-1)]
def val(f,x,m):
    acc=0
    for c in reversed(f): acc=mul(acc,x,m)^c
    return acc
def sat(rows,w):
    return all(any(((w>>(abs(x)-1))&1)==int(x>0) for x in row) for row in rows)
def run(net,states,raw_limit):
    m=net.mod
    B=net.B
    s=[1]
    for u in range(B): s=polyprod(s,[u,1],m)
    ps=[[1]]
    for j in range(1,B//2): ps.append(polyprod(ps[-1],s,m))
    basis=[[0]*b+ps[j] for j in range(B//2) for b in range(B)]
    assert all(len(p)==j+1 and p[-1]==1 for j,p in enumerate(basis))
    code=[xor(g for j,g in enumerate(net.inner) if x>>j&1) for x in range(net.Q)]
    assert len(set(code))==net.Q and min(w.bit_count() for w in code[1:])>=net.h//2
    for x,w in enumerate(code):
        assert net.inner_entry(x,w) and not net.inner_entry(x,w^1)
    total=accepted=0
    for seed in states:
        coeff=[xor(mul(a,p[j],m) for a,p in zip(seed,basis) if j<len(p)) for j in range(net.K)]
        assert tuple(coeff)==net.monomial(seed)
        reverse=coeff[:]
        for j in reversed(range(net.K)):
            a=reverse[j]
            assert a==seed[j]
            for k,c in enumerate(basis[j]): reverse[k]^=mul(a,c,m)
        direct=[val(coeff,x,m) for x in range(net.Q)]
        assert tuple(direct)==net.stages(seed)
        f=[]
        for b in range(B):
            v=[val(seed[b::B],val(s,t,m),m) for t in net.reps]
            assert net.first_entry(seed[b::B],v) and not net.first_entry(seed[b::B],[v[0]^1,*v[1:]]) and not net.first_entry(seed[b::B],v[:-1])
            f.append(v)
        for i,t in enumerate(net.reps):
            v=direct[t:t+B]
            inp=[f[b][i] for b in range(B)]
            assert net.second_entry(i,inp,v) and not net.second_entry(i,inp,[v[0]^1,*v[1:]])
        residual=[(-(net.ell*i+t+1),net.ell*((i+1)%net.Q)+t+1,net.ell*((i+2)%net.Q)+t+1) for i in range(net.Q) for t in range(net.ell)]
        out=sum(code[v]<<(i*net.ell) for i,v in enumerate(direct))
        accepted+=sat(residual,out)
        if total<raw_limit:
            physical=net.raw_witness(seed,residual)
            assert physical['accepted']==sat(residual,out)==sat(physical['clauses'],physical['word'])
            wires=physical['clauses'][:-len(residual)]
            assert sat(wires,physical['word']) and not sat(wires,physical['word']^(1<<(physical['n']-1)))
            readout=sum(((physical['word']>>(v-1))&1)<<i for i,v in enumerate(physical['outputs']))
            assert readout==out
            # Pinning only a proper subset of COPY replicas leaves extra assignments;
            # with all equality edges in place there is one extension for each input.
            for bit in (0,1):
                assert sum(a==bit and b==a and c==a for a,b,c in itertools.product((0,1),repeat=3))==1
                assert sum(a==bit and b==a for a,b,c in itertools.product((0,1),repeat=3))==2
        total+=1
    return total,accepted
rng=random.Random(4819)
large=run(rs.Network(4),[[0]*8]+[[rng.randrange(16) for _ in range(8)] for j in range(24)],3)
import rs_coset_entries_small as small
assert sha(small.__file__)=='c2f62b6bc28f747fda22f3220b649d9d8484c131c6bc7682f8764f8003a3fc53'
tiny=run(small.Network(2),itertools.product(range(4),repeat=2),16)
net=rs.Network(4)
# Pin the 28 higher monomial-coefficient bits. The four free bits are exhaustive.
slice_counts=[0,0]
for a in range(16):
    obj=net.raw_witness([a]+[0]*7,[(1,1)])
    original_pins=[(-j,) for j in range(5,33)]
    slice_counts[0]+=sat((*obj['clauses'],*original_pins),obj['word'])
    slice_counts[1]+=net.encode(a)&1
assert slice_counts==[8,8]
guard()
signal.setitimer(signal.ITIMER_PROF,0)
print(json.dumps(dict(checker=sha(__file__),target=sha(rs.__file__),tiny_target=sha(small.__file__),gf4=tiny,gf16=large,four_bit_slice=slice_counts,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

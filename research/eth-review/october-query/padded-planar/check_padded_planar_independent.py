"""Call the public counter, using original truth-table and independent spin oracles."""
import fcntl,hashlib,json,random,resource,signal,time
from itertools import combinations
from pathlib import Path
from math import comb,prod
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.025,.025)
import networkx
import padded_planar_solver as uut
def digest(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
src=digest(uut.__file__)
assert src=='4b697c8940d09e3e5211c1d4c5c27c3bfec37c206fde1ace4c8b83aadbaf4ced'
rng=random.Random(6541)
def build(v,edges,pads,unused=0):
    n=v
    rows=[]
    for (i,j),b in zip(edges,pads):
        for s in (1,-1):
            block=list(range(n+1,n+2+b))
            n+=1+b
            rows.append([s*(i+1),s*(j+1),block[0]])
            rows.extend([[-u for u in t] for t in combinations(block,3)])
    n+=unused
    perm=list(range(1,n+1))
    rng.shuffle(perm)
    rows=[[perm[abs(x)-1]*(1 if x>0 else -1) for x in row] for row in rows]
    for row in rows:rng.shuffle(row)
    rng.shuffle(rows)
    return n,rows
def bitcount_original(n,rows):
    full=(1<<(1<<n))-1
    words=[]
    for i in range(n):
        s=1<<i
        a=((1<<s)-1)<<s
        k=2*s
        while k<1<<n:
            a |= a<<k
            k*=2
        words.append(a)
    keep=full
    for row in rows:
        clause=0
        for lit in row:
            u=words[abs(lit)-1]
            clause |= u if lit>0 else full^u
        keep &=clause
    return keep.bit_count()
def spin(v,edges,pads):
    total=0
    for x in range(1<<v):
        vec=[]
        for (i,j),b in zip(edges,pads):
            # Enumerate a *single* sector's gated clique directly by weights.
            fixed=[sum(comb(b,r) for r in range(b+1) if r+z<=2) for z in (0,1)]
            xi,xj=(x>>i)&1,(x>>j)&1
            vec.append(sum(w for z,w in enumerate(fixed) if xi or xj or z)
                       *sum(w for z,w in enumerate(fixed) if not xi or not xj or z))
        total+=prod(vec)
    return total
tri=[(0,1),(1,2),(2,0)]
wheel=[(0,1),(1,2),(2,3),(3,0)]+[(i,4) for i in range(4)]
log=[]
for name,v,edges,pads,u,do_truth in [
    ('triangle',3,tri,[2,2,2],0,True),('mixed_triangle',3,tri,[2,3,2],2,False),
    ('bridge',6,tri+[(3,4),(4,5),(5,3),(1,3)],[2]*7,1,False),('wheel',5,wheel,[2,3,2,4,2,2,3,2],3,False)]:
    n,rows=build(v,edges,pads,u)
    want=spin(v,edges,pads)<<u
    if do_truth: assert want==bitcount_original(n,rows)
    got=uut.count(n,rows)
    assert got==want,(name,got,want)
    log.append([name,n,len(rows),got])
n,rows=build(3,tri,[2]*3)
idx=next(i for i,row in enumerate(rows) if all(l<0 for l in row))
for bad in (rows+[rows[0]],rows[:idx]+rows[idx+1:],rows+[[1,2]],rows+[[1,-1,2]]):
    assert uut.count(n,bad) is None
try:uut.count(n,rows+[[1,2,0]])
except ValueError:pass
else:raise AssertionError('invalid literal accepted')
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(solver=src,checker=digest(__file__),counts=log,malformed=5,networkx=networkx.__version__,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,cpu_s=time.process_time())))

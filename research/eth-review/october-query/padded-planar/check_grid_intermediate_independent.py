"""Truth-count raw sparse-check syndromes; compare final CNF and signed 3x3 partitions."""
import fcntl,resource,signal,time,json,hashlib,random
from pathlib import Path
from itertools import product,combinations
from math import prod
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_): assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 64*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,.02,.02)
import padded_grid_intermediate as uut
import padded_planar_solver as final
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
source=sha(uut.__file__)
assert source=='2801be2918170521a312088aae15232cc03059fd85862400f4193ce7da8adb79'
assert sha(Path(uut.__file__).with_name('padded_intermediate.py'))=='ce5f0e96481e016bce87028599a4f0dabc9c09c4c39545d1663ecb15681d7a1a'
edges=[(1,2),(2,3),(3,4),(1,4)]
cnf=[]
n=4
for i,j in edges:
    for sign in (1,-1):
        z=n+1
        n+=3
        cnf += [[sign*i,sign*j,z],[-z,-(z+1),-(z+2)]]
n+=1 # explicitly contribute one unconstrained variable
def oracle(rows):
    ids=[i for i in range(len(cnf)) if any(r>>i&1 for r in rows)]
    used=sorted({abs(lit) for i in ids for lit in cnf[i]})
    freq=[0]*(1<<len(rows))
    for word in range(1<<len(used)):
        assignment={v:(word>>j)&1 for j,v in enumerate(used)}
        violation=sum(1<<i for i in ids if all(assignment[abs(l)]!=(l>0) for l in cnf[i]))
        syndrome=sum(((r&violation).bit_count()%2)<<j for j,r in enumerate(rows))
        freq[syndrome]+=1<<(n-len(used))
    return freq
A=1|2
B=4|16
trials=[]
for rows in [[],[0],[A,B],[A,B,A^B]]:
    expected=oracle(rows)
    for rhs,value in enumerate(expected):
        got,stats=uut.count(n,cnf,rows,rhs,budget=10000)
        assert got==value,(rows,rhs,got,value)
    assert sum(expected)==1<<n
    trials.append(expected)
final_count=final.count(n,cnf)
assert final_count==2*(70**4+28**4)
assert trials[2][0]!=final_count
rng=random.Random(945)
labels=list(range(30,39))
rng.shuffle(labels)
chart={(i,j):labels[3*i+j] for i in range(3) for j in range(3)}
factors={}
for (i,j),u in chart.items():
    for neighbor in [(i+1,j),(i,j+1)]:
        if neighbor in chart:
            edge=tuple(sorted((u,chart[neighbor])))
            factors[edge]=[rng.choice([-3,-2,-1,1,2,3]) for _ in range(4)]
def signed_sum():
    total=0
    for bits in product((0,1),repeat=9):
        x=dict(zip(labels,bits))
        total+=prod(f[x[u]+2*x[v]] for (u,v),f in factors.items())
    return total
signed=signed_sum()
assert uut.partition(3,chart,factors)==signed and signed!=0
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(solver=source,checker=sha(__file__),n=n,syndrome_counts=trials,final_original=final_count,signed_unrestricted_partition=signed,cpu_s=time.process_time(),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

import fcntl, hashlib, json, resource, signal, time
from itertools import combinations
from pathlib import Path
lock=open('/workspace/scratch/pnp-native-search.lock','a')
fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
resource.setrlimit(resource.RLIMIT_CPU,(4,4))
signal.alarm(9)
def guard(*_):
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 30*1024
signal.signal(signal.SIGPROF,guard)
signal.setitimer(signal.ITIMER_PROF,0.02,0.02)
import all_coset_recognizer as candidate
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()
candidate_sha=sha(candidate.__file__)
assert candidate_sha=='56d2c1c422db69c64c0617016f9605cc9741a9b01d04d744b33f8126b5058a35'
polys=[(sum(1<<i for i in triple),) for triple in combinations(range(5),3)]
# The determinant coordinates of an exterior three-vector cannot all vanish
# for three independent projected directions. Projection on the first five
# bits must have rank at most two, so codimension at least three is needed.
root_calls=[]
visited=set()
original_normals=candidate.normals
original_witness=candidate.cubic_witness
def audited_normals(dim,budget,triples):
    if dim==7:
        root_calls.append((budget,triples))
    yield from original_normals(dim,budget,triples)
def audited_witness(poly,n,basis,complement):
    visited.add(len(complement))
    return original_witness(poly,n,basis,complement)
candidate.normals=audited_normals
candidate.cubic_witness=audited_witness
w=candidate.recognize(7,polys,3)
assert w is not None and len(w)==4
points=[0]
for b in w:points.extend([x^b for x in points])
assert len(set(points))==16 and len({x&31 for x in points})==4
checks=0
for a,b,c in combinations(w,3):
    shifts=(0,a,b,c,a^b,a^c,b^c,a^b^c)
    for x in range(128):
        for m, in polys:
            assert sum(((x^v)&m)==m for v in shifts)%2==0
            checks+=1
assert candidate.recognize(7,polys,2) is None
assert root_calls[0][0]==3 and len(root_calls[0][1])==1 and len(set(root_calls[0][1][0]))==3
assert 3 in visited
guard()
signal.setitimer(signal.ITIMER_PROF,0)
signal.alarm(0)
print(json.dumps(dict(candidate=candidate_sha,checker=sha(__file__),root_rank=3,codim=3,lower_budget_no=True,third_differences=checks,returned=w,complement_depths=sorted(visited),cpu_s=time.process_time(),rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))

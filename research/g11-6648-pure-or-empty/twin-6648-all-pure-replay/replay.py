"""Independent bounded replay. Run only under the scheduled lock handoff."""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import signal
import sys
import time

ROOT = Path(__file__).resolve().parent
LOCK = Path('/workspace/scratch/pnp-native-search.lock')
EXPECTED = (27, 193638)
ISSUED = Path('/tmp/pnp-new-exact-6648.json')
PIN = 'daddfc9d4602b1e19c9b153e45bae92fba851b6b6467a184f3409977f34e44fb'

def digest(data):
    return hashlib.sha256(data).hexdigest()

def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length()-1
        mask ^= low

def prepare():
    statement = json.loads(ISSUED.read_bytes())['formal_statement']
    assert digest(statement.encode()) == PIN
    edges = [tuple(map(int,p)) for p in re.findall(r'\(\((\d+) : ℕ\), \((\d+) : ℕ\)\)',statement)]
    assert len(edges)==16
    candidates = [edge for edge in edges if 3 not in edge]
    H = set(range(11)) - {3,6,7}
    mask = lambda vertices: sum(1<<i for i in vertices)
    full = (1<<11)-1
    neighbors = [0]*11
    for u,v in edges:
        neighbors[u] |= 1<<v
        neighbors[v] |= 1<<u
    complement = [full ^ (1<<v | neighbors[v]) for v in range(11)]
    maximal = []
    def cliques(r,p,x):
        if not (p|x):
            maximal.append(r)
        while p:
            v = (p&-p).bit_length()-1
            bit = 1<<v
            cliques(r|bit,p&complement[v],x&complement[v])
            p ^= bit
            x |= bit
    cliques(0,full,0)
    assert len(set(maximal))==len(maximal)==24

    # Minimal, actual permitted raw port words; take all unions.
    generators = [1<<v for v in H]+[mask((6,9)),mask((7,10))]+[mask((6,7,v)) for v in H]
    catalogue = {0}
    for atom in generators:
        catalogue |= {s|atom for s in catalogue}
    supports = sorted(catalogue-{0}, key=lambda s:(s.bit_count(),s))
    witnesses=[]; blockers=[]; dominated=[]; hits=[0]*14
    for i,s in enumerate(supports):
        witnesses.append(sum(1<<j for j,I in enumerate(maximal) if s&I==0))
        blockers.append([sum(1<<j for j,(a,b) in enumerate(candidates) if
                         (a==center and s>>b&1) or (b==center and s>>a&1))
                         for center in H if s & ~mask(H)==0 and s & ~neighbors[center]==0])
        dominated.append(sum(1<<j for j,t in enumerate(supports) if t&s==s))
        for j,(a,b) in enumerate(candidates):
            if s>>a&1 or s>>b&1:
                hits[j] |= 1<<i
    return supports,witnesses,blockers,dominated,hits,(1<<len(maximal))-1

def solve(R, data):
    supports, witnesses, blockers, dominated, hits, full = data
    available = (1<<len(supports))-1
    for edge in bits(R):
        available &= hits[edge]
    rows = []
    while available:
        j = (available&-available).bit_length()-1
        available &= ~dominated[j]
        if witnesses[j]:
            cost = 1 if supports[j].bit_count()==1 or any(R&bar==0 for bar in blockers[j]) else 2
            rows.append((witnesses[j],cost))
    # Delete supersets of raw support above, rather than dominated rejection masks.
    rows.sort(key=lambda option:-option[0].bit_count())
    suffix = [0]*(len(rows)+1)
    for j in reversed(range(len(rows))):
        suffix[j] = suffix[j+1] | rows[j][0]
    if suffix[0]!=full:
        return 255
    # Include or omit the next support; identical accumulated rejected sets
    # keep only their cheapest cost. Suffix union discards impossible branches.
    frontier = {0:0}
    for j,(covered,cost) in enumerate(rows):
        next_states = {}
        for state,price in frontier.items():
            for after,paid in ((state,price),(state|covered,price+cost)):
                if after|suffix[j+1]==full and paid<next_states.get(after,255):
                    next_states[after]=paid
        frontier = next_states
    return frontier[full]

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('start',type=int)
    parser.add_argument('end',type=int)
    args=parser.parse_args()
    assert 1<=args.start<=args.end<=16383
    ledger=ROOT/'tranches.jsonl'
    prior=[json.loads(s) for s in ledger.read_text().splitlines()] if ledger.exists() else []
    assert args.start==(prior[-1]['next'] if prior else 1)
    start_wall=time.monotonic(); start_cpu=time.process_time()
    def identity(stat):return stat.st_dev,stat.st_ino
    assert identity(LOCK.stat())==EXPECTED
    with LOCK.open('rb') as handle:
        fd=handle.fileno()
        assert identity(os.fstat(fd))==EXPECTED
        fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
        def guard():
            assert identity(LOCK.stat())==identity(os.fstat(fd))==EXPECTED
            assert any(line.split()[1:6]==['FLOCK','ADVISORY','WRITE',str(os.getpid()),'00:1b:193638']
                       for line in Path('/proc/locks').read_text().splitlines())
        guard()
        resource.setrlimit(resource.RLIMIT_AS,(64*1024**2,64*1024**2))
        resource.setrlimit(resource.RLIMIT_CPU,(3,3))
        signal.setitimer(signal.ITIMER_REAL,5.95)
        data=prepare()
        start=args.start
        score_hash=hashlib.sha256()
        deficient=[]
        last=start-1
        for R in range(start,args.end+1):
            cost=solve(R,data)
            score_hash.update(bytes([cost]))
            if cost<R.bit_count():
                deficient.append([R,R.bit_count(),cost])
            last=R
            if time.process_time()-start_cpu>=2.50 or time.monotonic()-start_wall>=5.20:
                break
        guard()
        record=dict(start=start,end=last,next=last+1,deficient=deficient,
                    covered=last-start+1,score_bytes_sha256=score_hash.hexdigest(),source=digest(Path(__file__).read_bytes()),
                    statement=PIN,lock=list(EXPECTED),pid=os.getpid(),cpu=time.process_time()-start_cpu,
                    wall=time.monotonic()-start_wall,maxrss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
        with ledger.open('a') as out:
            out.write(json.dumps(record,sort_keys=True)+'\n');out.flush();os.fsync(out.fileno())
        print(json.dumps(record),flush=True)
        fcntl.flock(fd,fcntl.LOCK_UN)
if __name__=='__main__':
    main()

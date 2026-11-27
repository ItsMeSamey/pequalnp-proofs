"""Exact coverage by bit-mask intersections of local stabilizer-bra sets."""
from collections import Counter
from pathlib import Path
import sys
import numpy as np
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'g3-complex-conic-search'))
from search import stabs,orbit_reps,p,pivots,unit

def bits(a):
    return int.from_bytes(np.packbits(a,bitorder='little').tobytes(),'little')

def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length()-1
        mask ^= bit

def main():
    rays=stabs()
    orbits=orbit_reps(rays)
    U=np.array([[0 if e<0 else (1,0,-1,0)[e] for e in r] for r in rays],dtype=np.int16)
    V=np.array([[0 if e<0 else (0,1,0,-1)[e] for e in r] for r in rays],dtype=np.int16)
    ev=(U@U.T+V@V.T!=0)|(U@V.T-V@U.T!=0)
    g=np.array([1]*7+[-1],dtype=np.int64)
    good=(U@g!=0)|(V@g!=0)
    order=np.random.default_rng(1).permutation(len(rays))
    nonorth=[bits(row) for row in ev]
    orth=[bits((good&~row)[order]) for row in ev]
    M=np.array([[0 if e<0 else unit[e] for e in r] for r in rays],dtype=np.int64)
    allmask=(1<<len(rays))-1
    stats=Counter()
    bad=[]
    for a,_ in orbits:
        for b in range(len(rays)):
            stats['pairs']+=1
            candidates=allmask
            for k in indices(orth[a]&orth[b]):
                candidates &= nonorth[int(order[k])]
                if not candidates: break
            if not candidates: continue
            A=M[[a,b]]
            if len(pivots(np.vstack([A,g]),p))==len(pivots(A,p)):
                assert candidates==allmask
                stats['pair spans g']+=1
                continue
            for c in indices(candidates):
                C=M[[a,b,c]]
                if len(pivots(np.vstack([C,g]),p))>len(pivots(C,p)):
                    stats['failure outside span']+=1
                    if len(bad)<10: bad.append((a,b,c))
                else: stats['failure in span']+=1
    print('rays',len(rays),'good bras',sum(good),'first-ray orbits',len(orbits),dict(stats),'counterexamples',bad)
if __name__=='__main__':main()

"""Generate exact signed samples for the degree-one terminal minor."""
import argparse
import json
from itertools import combinations
from pathlib import Path
import sys
from sample import samples
ROOT=Path(__file__).resolve().parent

DEGREE_ONE={2:5,8:1,16:2,32:3}
MASK=(1<<38)-1

def dataset(peeled):
    if len(peeled)!=len(set(peeled)) or not set(peeled)<=set(DEGREE_ONE):
        raise ValueError('invalid peeled points')
    raw,seed,target=samples(ROOT/'L-meta-18968.json')
    positives={r&MASK for i,r in enumerate(raw) if target>>i&1 and not seed>>i&1}
    negatives={r&MASK for i,r in enumerate(raw) if not target>>i&1}
    removed=sum(peeled)
    wires=[i for i in range(38) if not removed>>i&1]
    def compact(r):
        return sum((r>>i&1)<<j for j,i in enumerate(wires))
    pos={compact(r) for r in positives if not r&removed}
    forced={compact(r) for r in positives if r&removed}
    neg={compact(r) for r in negatives}|forced
    maxima=sorted(n for n in neg if not any(n!=m and not n&~m for m in neg))
    assert len(pos)==28-len(peeled)
    assert not any(not p&~n for p in pos for n in maxima)
    for j in range(7):
        flag=1<<wires.index(13+j)
        assert any((p&~n)==flag for p in pos for n in maxima)
    return dict(peeled=list(peeled),gate_bound=33-2*len(peeled),original_wire_ids=wires,
                positives=sorted(pos),forced_negatives=sorted(forced),maximal_negatives=maxima)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--peeled',type=int,nargs='*',default=[])
    ap.add_argument('--all',action='store_true')
    args=ap.parse_args()
    if args.all:
        for k in range(5):
            for e in combinations(DEGREE_ONE,k):
                d=dataset(e);print(e,d['gate_bound'],len(d['positives']),len(d['maximal_negatives']))
    else:print(json.dumps(dataset(args.peeled)))

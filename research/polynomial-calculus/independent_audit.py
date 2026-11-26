"""Independent multilinear PC fixed point; only stdlib and input JSON."""
from itertools import combinations
from pathlib import Path
from json import loads


def insert(B, v):
    while v:
        lead = v.bit_length() - 1
        if lead not in B:
            B[lead] = v
            return True
        v ^= B[lead]
    return False


def indices(v):
    while v:
        low = v & -v
        yield low.bit_length()-1
        v ^= low


def audit(path):
    spec = loads(path.read_text())
    rows, off, mark = (spec[k] for k in ('matrix','offset','marker'))
    n = len(rows)
    mons = [sum(1<<j for j in s) for d in range(4) for s in combinations(range(n),d)]
    pos = {m:i for i,m in enumerate(mons)}
    B = {}
    for i,row in enumerate(rows):
        eq = (1 << pos[1<<i]) if off>>i & 1 else 0
        for j in indices(row):
            eq ^= 1 << pos[(1<<i)|(1<<j)]
        insert(B,eq)
    if mark is not None:
        insert(B,1 | sum(1<<pos[1<<i] for i in indices(mark)))
    histories = [len(B)]
    while True:
        old = tuple(B.values())
        for i in range(n):
            xi = 1<<i
            # A cubic missing x_i has its own unique quartic image.
            forbidden = sum(1<<j for j,m in enumerate(mons) if m.bit_count()==3 and not m&xi)
            pivots = {}
            for v in old:
                while v & forbidden:
                    lead = (v & forbidden).bit_length()-1
                    if lead not in pivots:
                        pivots[lead] = v
                        break
                    v ^= pivots[lead]
                else:
                    w = 0
                    for j in indices(v):
                        w ^= 1 << pos[mons[j]|xi]
                    insert(B,w)
        if len(B)==len(old):
            break
        histories.append(len(B))
    provided = [sum(1 << pos[m] for m in terms) for terms in spec['space_basis']]
    C = {}
    for v in provided:
        insert(C,v)
    assert len(C)==len(B) and all(not insert(C,v) for v in B.values())
    contains_one = 0 in B
    print(path.name, 'ambient',len(mons),'dimensions',histories,'contains 1:',contains_one)
    assert not contains_one
    if n==11:
        assert insert(dict(B),1 << pos[1<<10]), 'forced bit was derivable'
        models=[x for x in range(1<<n) if all(not (x>>i&1) or (row&x).bit_count()%2==(off>>i&1) for i,row in enumerate(rows))]
        assert models and all(x < 1024 for x in models)
        print('base models',len(models),'all force x10=0')
    else:
        base=loads(path.with_name('affine-base.json').read_text())
        assert n==22 and rows==base['matrix']+[a<<11 for a in base['matrix']]
        assert off==(base['offset'] | base['offset']<<11) and mark==((1<<10)|(1<<21))
        print('disjoint copies and XOR marker verified')


if __name__=='__main__':
    for f in ['affine-base.json','unsat-marker.json']:
        audit(Path(__file__).with_name(f))

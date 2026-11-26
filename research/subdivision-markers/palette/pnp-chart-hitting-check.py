"""Small comparisons against literal physical spans, plus seed-family checks."""
from pathlib import Path
from itertools import combinations
from random import Random
from runpy import run_path

solver = run_path(str(Path(__file__).with_name("pnp-chart-hitting.py")))
rng = Random(61097)

def sums(values):
    result={0}
    for v in values:
        result |= {v^x for x in result}
    return result

def physical_truth(columns):
    spans={frozenset({0})}
    for k,b,h in columns:
        v=(k<<4)|(b<<2)|h
        spans |= {s|frozenset(v^x for x in s) for s in spans}
    return any({x for x in s if x<16}==set(range(4)) for s in spans)

tested=0
for d in (0,1,2,3):
    for case in range(14):
        cols=[(1<<i,rng.randrange(4),rng.randrange(4)) for i in range(d)]
        cols += [(rng.randrange(1<<d),rng.randrange(4),rng.randrange(4)) for _ in range(7)]
        if case%2:
            cols.extend([(1<<i,b,rng.randrange(4)) for i in range(min(1,d)) for b in range(4)])
        if case%3==0:
            cols += [(0,0,1),(0,0,2)]
        answer=solver['solve'](cols,d,direct=bool(case%2))
        assert (answer is not None)==physical_truth(cols)
        if answer is not None:
            physical=sums([(cols[i][0]<<4)|(cols[i][1]<<2)|cols[i][2] for i in answer])
            assert {x for x in physical if x<16}==set(range(4))
            assert len(answer)<=d+2
        tested+=1
print(tested,'literal physical comparisons passed')
m=9
s=solver['seeds'](m,1)
for normal in range(1,1<<m):
    for side in (0,1):
        subset=[v for v in s if (v&normal).bit_count()%2==side]
        assert subset and solver['rank'](v^subset[0] for v in subset)==m-1
print('affine spans checked for',2*((1<<m)-1),'hyperplanes;',len(s),'seed points')

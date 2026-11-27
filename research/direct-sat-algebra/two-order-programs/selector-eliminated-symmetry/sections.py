"""Exact bounded elimination with original-bit fiber sections."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'selector-prefix-automorphism'))
from swaps import signed_swaps

def index(word,s):
    return sum(((word>>(v-1))&1)<<j for j,v in enumerate(s))

def unpack(i,s):
    return sum(((i>>j)&1)<<(v-1) for j,v in enumerate(s))

def prepare(n,clauses,front,*,width=4):
    if width<0 or n<0 or front<0 or front>>n: raise ValueError('invalid chart')
    tables={};seen=set()
    for c in clauses:
        c=tuple(c)
        if any(not 1<=abs(v)<=n for v in c): raise ValueError('bad variable')
        if any(-v in c for v in c): continue
        s=tuple(sorted(set(map(abs,c))))
        if len(s)>3: raise ValueError('expected width at most three')
        seen.update(s)
        i=sum(1<<j for j,v in enumerate(s) if -v in c)
        tables[s]=tables.get(s,(1<<(1<<len(s)))-1)&~(1<<i)
    steps=[]
    while True:
        choices=[]
        for v in seen:
            if front>>(v-1)&1: continue
            bucket=[s for s in tables if v in s]
            scope=sorted({u for s in bucket for u in s})
            if len(scope)<=width: choices.append((len(scope),v,bucket,scope))
        if not choices: break
        _,v,bucket,scope=min(choices)
        rest=tuple(u for u in scope if u!=v)
        vals=[]
        for i in range(1<<len(rest)):
            word=unpack(i,rest)
            vals.append(sum(1<<b for b in (0,1) if all(
                tables[s]>>index(word|(b<<(v-1)),s)&1 for s in bucket)))
        for s in bucket: del tables[s]
        tab=sum(bool(val)<<i for i,val in enumerate(vals))
        if tab!=(1<<len(vals))-1: tables[rest]=tables.get(rest,(1<<len(vals))-1)&tab
        seen.remove(v)
        steps.append((v,rest,tuple(vals)))
    return tables,steps,list(signed_swaps(n,tables,front))

def lift_word(word,steps):
    for v,rest,vals in reversed(steps):
        allowed=vals[index(word,rest)]
        if not allowed: raise ValueError('infeasible residual assignment')
        word=(word&~(1<<(v-1)))|(int(not allowed&1)<<(v-1))
    return word

def transform(word,g,steps):
    a,b,shift=g
    if a and ((word>>(a-1))^(word>>(b-1)))&1:
        word^=(1<<(a-1))|(1<<(b-1))
    return lift_word(word^shift,steps)

"""Source-level exact joint shifts relative to individual tail-scope symmetries."""
from dataclasses import dataclass
from pathlib import Path
import sys
root=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(root/'cnf-common-tables'))
from route import Basis,horn_model,affine
sys.path.insert(0,str(root/'cnf-two-state'))
from recognizer import normalize

@dataclass(frozen=True)
class Answer:
    status:str
    shift:int|None
    modes:tuple
    scopes:int
    work:int

class Refused(Exception): pass
class Meter:
    def __init__(self,limit): self.limit=limit;self.used=0
    def charge(self,k=1):
        if self.used+k>self.limit: raise Refused
        self.used+=k

def grouped(rows):
    groups={}
    for r in rows:
        scope=tuple(sorted(abs(l)-1 for l in r))
        bad=sum((1<<i) for i,v in enumerate(scope) if -(v+1) in r)
        groups.setdefault(scope,set()).add(bad)
    return groups

def spread(x,scope): return sum((1<<v) for i,v in enumerate(scope) if x&(1<<i))
def bit(a,x): return (a&x).bit_count()%2

def xor_equations(scope,left,right,rows,meter):
    shifts=[]
    for s in range(1<<len(scope)):
        meter.charge(1+len(left))
        if len(left)==len(right) and all((x^s) in right for x in left): shifts.append(s)
    if not shifts: return False
    eq=affine(scope,shifts)
    if eq is None: raise AssertionError("local transition set is not a coset")
    return all(rows.add(a,b) for a,b in eq)

def condition(rows,pins):
    fixed={abs(l):l for l in pins}
    if len(fixed)!=len(set(pins)): return ((),)
    return tuple(tuple(l for l in r if -l!=fixed.get(abs(l))) for r in rows if not any(l==fixed.get(abs(l)) for l in r))

def horn_rules(rows):
    rules=[]
    for r in rows:
        pos=[l for l in r if l>0]
        if len(pos)>1: raise Refused
        rules.append((tuple(-l-1 for l in r if l<0),pos[0]-1 if pos else None))
    return rules

def project_horn(rows,B,a,meter):
    horn_rules(rows)
    current={frozenset(r) for r in rows}
    while True:
        private={abs(l)-1 for r in current for l in r}-B
        if not private: return tuple(tuple(r) for r in current)
        for v in sorted(private):
            meter.charge(1+len(current))
            hit=[r for r in current if v+1 in r or -v-1 in r]
            names={abs(l)-1 for r in hit for l in r}-{v}
            if len(names)>a: continue
            up=[r-{v+1} for r in hit if v+1 in r]; down=[r-{-v-1} for r in hit if -v-1 in r]
            meter.charge(len(up)*len(down))
            current.difference_update(hit)
            for p in up:
                for q in down:
                    new=p|q
                    if not any(-l in new for l in new): current.add(new)
            break
        else: raise Refused

def join(n,prefix,tail,boundary,first_pins,second_pins,*,fixed=(),arity=3,cap=1000000):
    if any(type(v)!=int or v<0 for v in (n,cap,arity)): raise ValueError("invalid limit")
    B={v-1 for v in boundary}
    if any(i<0 or i>=n for i in B): raise ValueError("invalid boundary variable")
    pre=normalize(n,prefix); suff=normalize(n,tail)
    # Private and selector names must not silently reappear in the suffix.
    if ({abs(l)-1 for r in pre for l in r}&{abs(l)-1 for r in suff for l in r})-B:
        raise ValueError("an actual shared variable is missing from the boundary")
    pins=[tuple(p) for p in (first_pins,second_pins)]
    for p in pins:
        if any(type(l)!=int or not 1<=abs(l)<=n or abs(l)-1 in B for l in p):
            raise ValueError("invalid/private pin overlaps boundary")
    if {abs(l) for l in pins[0]}!={abs(l) for l in pins[1]}: raise ValueError("prefix pin sets differ")
    meter=Meter(cap); count=0
    def answer(status,shift=None): return Answer(status,shift,("HORN","HORN"),count,meter.used)
    try:
        if any(len(r)>arity for r in (*pre,*suff)): raise Refused
        projections=[project_horn(condition(pre,p),B,arity,meter) for p in pins]
        sets=[horn_rules(rs) for rs in projections]
        rows=Basis()
        for v in fixed:
            if type(v)!=int or not 1<=v<=n: raise ValueError("invalid immutable variable")
            rows.add(1<<(v-1),0)
        for sc,bads in grouped(suff).items():
            # Translation of forbidden set is equivalent to translation of allowed set.
            if not xor_equations(sc,bads,bads,rows,meter): raise AssertionError("zero lift missing")
        feasible=[horn_model(r) is not None for r in sets]
        if feasible[0]!=feasible[1]: return answer("NO_GROUP_LIFT")
        if not feasible[0]: return answer("LIFT",0)
        scopes=set(grouped(projections[0]))|set(grouped(projections[1]))
        for scope in sorted(scopes,key=lambda s:(len(s),s)):
            count+=1
            tables=[set(),set()]
            for x in range(1<<len(scope)):
                pinned=[((),v) if x&(1<<i) else ((v,),None) for i,v in enumerate(scope)]
                for j,r in enumerate(sets):
                    meter.charge(1+len(r)+len(pinned))
                    if horn_model(r+pinned) is not None: tables[j].add(x)
            if not xor_equations(scope,*tables,rows,meter): return answer("NO_GROUP_LIFT")
        return answer("LIFT",rows.lift())
    except Refused: return answer("SKIP")

def extend_horn(n,prefix,pins,boundary_values):
    """Recover a raw prefix assignment; input signed pins and boundary literals are true."""
    raw=normalize(n,prefix)
    forced=tuple(pins)+tuple(boundary_values)
    reduced=condition(raw,forced)
    w=horn_model(horn_rules(reduced))
    if w is None: return None
    for l in forced:
        if l>0: w|=1<<(l-1)
        else: w&=~(1<<(-l-1))
    if any(not any(bool(w&(1<<(abs(l)-1)))==(l>0) for l in r) for r in raw):
        raise AssertionError("prefix replay failed")
    return w

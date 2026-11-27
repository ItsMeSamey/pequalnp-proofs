"""Project components behind bounded separators, allowing growing bounded-width interiors."""
from itertools import combinations
from dataclasses import dataclass
from signed_cover_projection import normalized,sat

@dataclass(frozen=True)
class Projection:
    n:int
    source:tuple
    core:tuple
    clauses:tuple
    pieces:tuple
    trace:tuple
    work:int

    def lift(self,word):
        if not 0<=word<1<<len(self.core): raise ValueError('bad core word')
        if not all(sat(c,word) for c in self.clauses): return None
        x=sum(((word>>i)&1)<<(v-1) for i,v in enumerate(self.core))
        for v,pos,neg in reversed(self.trace):
            one=any(not sat(c,x) for c in pos)
            zero=any(not sat(c,x) for c in neg)
            if one and zero: raise ArithmeticError('inconsistent trace')
            if one: x|=1<<(v-1)
        if not all(sat(c,x) for c in self.source): raise ArithmeticError('original witness mismatch')
        return x

class Limit(Exception): pass

def project(n,clauses,*,ports,width,budget,min_piece=2,max_piece=None,protected=()):
    if min(n,ports,width,budget)<0 or min_piece<1: raise ValueError('invalid limits')
    raw=tuple(tuple(c) for c in clauses)
    if any(not 1<=abs(x)<=n for c in raw for x in c): raise ValueError('bad raw variable')
    fixed=set(protected)
    if any(not 1<=x<=n for x in fixed): raise ValueError('bad protected variable')
    rows=normalized(raw)
    adj={}
    for c in rows:
        vs={abs(x) for x in c}
        for x in vs: adj.setdefault(x,set()).update(vs-{x})
    vertices=set(adj)
    work=0
    def pay(v=1):
        nonlocal work
        if v>budget-work: raise Limit
        work+=v
    def eliminate(local,inside):
        local=set(local)
        left=set(inside)
        steps=[]
        while left:
            choices=[]
            for x in left:
                pay(1+len(local))
                hit=[c for c in local if x in c or -x in c]
                neighbors={abs(t) for c in hit for t in c if abs(t)!=x}
                if len(neighbors)<=width: choices.append((len(neighbors),x,hit))
            if not choices: return None
            _,x,hit=min(choices,key=lambda t:t[:2])
            pos=tuple(c-{x} for c in hit if x in c)
            neg=tuple(c-{-x} for c in hit if -x in c)
            local.difference_update(hit)
            pay(len(pos)*len(neg)+1)
            for a in pos:
                for b in neg:
                    c=a|b
                    if not any(-t in c for t in c): local.add(c)
            steps.append((x,pos,neg))
            left.remove(x)
        return local,steps
    interiors=set()
    blocked=set(fixed)
    pieces=[]
    trace=[]
    output=set(rows)
    try:
        for k in range(min(ports,len(vertices))+1):
            for cut in combinations(sorted(vertices),k):
                pay(1+len(vertices)+sum(map(len,adj.values())))
                unseen=vertices-set(cut)
                while unseen:
                    start=min(unseen)
                    unseen.remove(start)
                    component={start}
                    stack=[start]
                    while stack:
                        fresh=adj[stack.pop()]&unseen
                        unseen-=fresh
                        stack.extend(fresh)
                        component.update(fresh)
                    if component&blocked or len(component)<min_piece or (
                           max_piece is not None and len(component)>max_piece): continue
                    pay(len(rows)+1)
                    hit={c for c in rows if any(abs(x) in component for x in c)}
                    found=eliminate(hit,component)
                    if found is None: continue
                    local,steps=found
                    output.difference_update(hit)
                    output.update(local)
                    trace.extend(steps)
                    boundary={abs(x) for c in hit for x in c}-component
                    pieces.append((tuple(sorted(component)),tuple(sorted(boundary))))
                    blocked.update(component|boundary)
                    interiors.update(component)
    except Limit: return None
    core=tuple(sorted(fixed|{abs(x) for c in output for x in c}))
    ids={x:i+1 for i,x in enumerate(core)}
    compressed=tuple(sorted(tuple(sorted((1 if x>0 else -1)*ids[abs(x)] for x in c)) for c in output))
    return Projection(n,raw,core,compressed,tuple(pieces),tuple(trace),work)

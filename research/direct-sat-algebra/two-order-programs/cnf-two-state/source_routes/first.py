"""Direct sparse-CNF and square dense-incidence fast paths, on declared original coordinates."""
from collections import defaultdict,deque
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent))
from recognizer import accepts,binary_model,discover,normalize

def fast(n,clauses,*,fallback=None):
    raw=tuple(tuple(c) for c in clauses)
    rows=normalize(n,raw)
    def accepted(route,w):
        if type(w) is not int or not 0 <= w < (1 << n):
            raise AssertionError("invalid original witness word")
        if not accepts(raw,w): raise AssertionError("original CNF replay failed")
        return "SAT",route,w
    if all(len(r)<=2 for r in rows):
        w=binary_model(n,rows)
        if w is None: return "UNSAT","SCC",None
        return accepted("SCC",w)
    active=[set(r) for r in rows]
    occurrences=defaultdict(list)
    todo=deque()
    for j,row in enumerate(active):
        if not row: return "UNSAT","UP",None
        for l in row: occurrences[l].append(j)
        if len(row)==1: todo.append(next(iter(row)))
    assigned=set()
    while todo:
        l=todo.popleft()
        if -l in assigned: return "UNSAT","UP",None
        if l in assigned: continue
        assigned.add(l)
        for j in occurrences[l]: active[j]=None
        for j in occurrences[-l]:
            row=active[j]
            if row is None: continue
            row.remove(-l)
            if not row: return "UNSAT","UP",None
            if len(row)==1: todo.append(next(iter(row)))
    residual=[tuple(row) for row in active if row is not None]
    fixed=sum(1<<(l-1) for l in assigned if l>0)
    touched=sum(1<<(abs(l)-1) for l in assigned)
    if not residual: return accepted("UP",fixed)
    if all(len(row)<=2 for row in residual):
        extra=binary_model(n,residual)
        if extra is None: return "UNSAT","UP+SCC",None
        return accepted("UP+SCC",(extra&~touched)|fixed)
    if fallback is None: return "SKIP","RESIDUAL",None
    # Use untouched raw rows so supplied original clause indices and witnesses remain valid.
    result,w,_=fallback(n,raw)
    if result=="SAT": return accepted("FALLBACK",w)
    if result=="UNSAT": return "UNSAT","FALLBACK",None
    return "SKIP","FALLBACK",None

def dense(d,positive,negative,domain0,domain1,*,fallback=None):
    if type(d) is not int or d<1 or len(positive)!=d or len(negative)!=d: raise ValueError("bad dimensions")
    mask=(1<<d)-1
    if any(type(v) is not int or v<0 or v>mask for v in (*positive,*negative,domain0,domain1)):
        raise ValueError("invalid incidence or domain vector")
    if domain0|domain1 != mask: return "UNSAT","DOMAIN",None
    rows=[]
    def positions(bits):
        while bits:
            l=bits&-bits
            yield l.bit_length()
            bits-=l
    for p,q in zip(positive,negative):
        if p&q: continue
        rows.append(tuple(positions(p))+tuple(-i for i in positions(q)))
    rows.extend((i,) for i in positions(mask^domain0))
    rows.extend((-i,) for i in positions(mask^domain1))
    status,route,w=fast(d,rows,fallback=fallback)
    if status=="SAT":
        if w&~domain1 or (~w)&mask&~domain0: raise AssertionError("original domain replay failed")
        if any(not ((p&w)|(q&~w)) for p,q in zip(positive,negative)): raise AssertionError("original incidence replay failed")
    return status,route,w

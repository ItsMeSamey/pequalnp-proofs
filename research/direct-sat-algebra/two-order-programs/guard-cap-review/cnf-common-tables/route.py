"""Source-first exact common affine, Horn or bijunctive equal-scope CNF tables."""
from collections import defaultdict,deque
from dataclasses import dataclass
from itertools import combinations
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'cnf-two-state'))
from recognizer import binary_model

@dataclass(frozen=True)
class Result:
    status:str
    route:str
    witness:int|None
    scopes:int
    cells:int
    source_clauses:int
    source_literals:int
    generated:int

class Basis:
    def __init__(self): self.rows={}
    def add(self,x,b):
        while x:
            i=x.bit_length()-1
            if i not in self.rows:
                self.rows[i]=(x,b)
                return True
            y,c=self.rows[i]
            x^=y; b^=c
        return b==0
    def lift(self,w=0):
        for i,(a,b) in sorted(self.rows.items()):
            if (a&w).bit_count()%2!=b: w ^= 1<<i
        return w

def affine(scope,valid):
    base=valid[0]
    spans=Basis()
    for x in valid: spans.add(x^base,0)
    if len(valid) != 1<<len(spans.rows): return None
    equations=[]
    for i in range(len(scope)):
        if i in spans.rows: continue
        normal=spans.lift(1<<i)
        mask=sum(1<<j for k,j in enumerate(scope) if normal>>k&1)
        equations.append((mask,(base&normal).bit_count()%2))
    return equations

def horn(scope,valid):
    a=len(scope); size=1<<a
    meet=[size]*size
    for x in valid: meet[x]=x
    for i in range(a):
        bit=1<<i
        for x in range(size):
            if x&bit: continue
            other=meet[x|bit]
            if other!=size: meet[x]=other if meet[x]==size else meet[x]&other
    accepted=set(valid)
    implications=[]
    for x in range(size):
        if x in accepted: continue
        common=meet[x]
        if common==x: return None
        head=None if common==size else scope[((common^x)&-(common^x)).bit_length()-1]
        implications.append((tuple(scope[i] for i in range(a) if x>>i&1),head))
    return implications

def binary(scope,valid):
    a=len(scope)
    choices=[(i,) for i in range(a)]+list(combinations(range(a),2))
    forbidden=[]
    for group in choices:
        mask=sum(1<<i for i in group)
        found={v&mask for v in valid}
        for value in range(1<<len(group)):
            bits=sum(((value>>k)&1)<<i for k,i in enumerate(group))
            if bits not in found:
                clause=tuple(-(scope[i]+1) if bits>>i&1 else scope[i]+1 for i in group)
                forbidden.append((mask,bits,clause))
    accepted=set(valid)
    for x in range(1<<a):
        if x not in accepted and not any(x&m==v for m,v,_ in forbidden): return None
    return [clause for _,_,clause in forbidden]

def horn_model(rules):
    needs=[len(lhs) for lhs,_ in rules]
    watch=defaultdict(list)
    pending=deque()
    for j,(lhs,head) in enumerate(rules):
        for v in lhs: watch[v].append(j)
        if not lhs: pending.append(head)
    ones=set()
    while pending:
        v=pending.popleft()
        if v is None: return None
        if v in ones: continue
        ones.add(v)
        for j in watch[v]:
            needs[j]-=1
            if not needs[j]: pending.append(rules[j][1])
    return sum(1<<v for v in ones)

def solve(n,clauses,*,arity=3,max_cells=65536):
    if any(type(x)!=int or x<0 for x in (n,arity,max_cells)):
        raise ValueError("invalid variable count or limits")
    raw=tuple(tuple(row) for row in clauses)
    literals=sum(map(len,raw))
    tables=defaultdict(set)
    for row in raw:
        if any(type(l)!=int or not 1<=abs(l)<=n for l in row): raise ValueError("invalid original literal")
        r=set(row)
        if any(-l in r for l in r): continue
        scope=tuple(sorted(abs(l)-1 for l in r))
        tables[scope].add(tuple(i+1 in r for i in scope))
    charged=0
    def finish(status,route,w=None,generated=0):
        if status=="SAT":
            if type(w)!=int or not 0<=w<1<<n: raise AssertionError("invalid original word")
            if not all(any(bool(w&(1<<(abs(l)-1)))==(l>0) for l in row) for row in raw):
                raise AssertionError("original CNF replay failed")
        return Result(status,route,w,len(tables),charged,len(raw),literals,generated)
    if any(len(s)>arity for s in tables): return finish("SKIP","ARITY")
    if sum(1<<len(s) for s in tables)>max_cells: return finish("SKIP","CELL_CAP")
    families={"AFFINE":[],"MEET":[],"MAJORITY":[]}
    for scope,patterns in tables.items():
        size=1<<len(scope)
        charged+=size
        forbidden={sum((not sign)<<i for i,sign in enumerate(pattern)) for pattern in patterns}
        valid=[x for x in range(size) if x not in forbidden]
        if not valid: return finish("UNSAT","EMPTY_TABLE")
        for name,fn in (("AFFINE",affine),("MEET",horn),("MAJORITY",binary)):
            if families[name] is not None:
                rows=fn(scope,valid)
                if rows is None: families[name]=None
                else: families[name].extend(rows)
    for name,rules in families.items():
        if rules is None: continue
        if name=="AFFINE":
            basis=Basis()
            w=basis.lift() if all(basis.add(a,b) for a,b in rules) else None
        elif name=="MEET":
            w=horn_model(rules)
        else:
            w=binary_model(n,rules)
        return finish("SAT" if w is not None else "UNSAT",name,w,len(rules))
    return finish("SKIP","NO_COMMON_CLASS")

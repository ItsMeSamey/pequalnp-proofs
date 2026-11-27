"""Any-order complete two-state factor recognition on original DIMACS variables."""
from dataclasses import dataclass

class Exhausted(Exception): pass

class Budget:
    def __init__(self, cap):
        if type(cap) is not int or cap < 0: raise ValueError("invalid operation budget")
        self.cap,self.used=cap,0
    def step(self):
        if self.used==self.cap: raise Exhausted
        self.used+=1

def normalize(n,rows):
    if type(n) is not int or n<0: raise ValueError("invalid variable count")
    result=set()
    for r in rows:
        r=set(r)
        if any(type(l) is not int or not 1<=abs(l)<=n for l in r): raise ValueError("invalid literal")
        if not any(-l in r for l in r): result.add(tuple(sorted(r,key=abs)))
    return tuple(sorted(result,key=lambda r:(len(r),r)))

def restrict(rows,l):
    return tuple(tuple(j for j in r if j!=-l) for r in rows if l not in r)

def binary_model(n,rows):
    graph=[[] for _ in range(2*n)]
    rev=[[] for _ in graph]
    for r in rows:
        if not r: return None
        a,b=(2*(abs(l)-1)+(l<0) for l in (r[0],r[-1]))
        for u,v in ((a^1,b),(b^1,a)):
            graph[u].append(v)
            rev[v].append(u)
    seen=set()
    order=[]
    for root in range(2*n):
        if root in seen: continue
        stack=[(root,0)]
        seen.add(root)
        while stack:
            v,i=stack[-1]
            if i==len(graph[v]):
                stack.pop()
                order.append(v)
                continue
            u=graph[v][i]
            stack[-1]=(v,i+1)
            if u not in seen:
                seen.add(u)
                stack.append((u,0))
    comp=[-1]*(2*n)
    for k,root in enumerate(reversed(order)):
        if comp[root]!=-1: continue
        stack=[root]
        comp[root]=k
        while stack:
            for u in rev[stack.pop()]:
                if comp[u]==-1:
                    comp[u]=k
                    stack.append(u)
    if any(comp[i]==comp[i+1] for i in range(0,2*n,2)): return None
    return sum((comp[2*i]>comp[2*i+1])<<i for i in range(n))

def sat(n,rows,budget):
    stack=[rows]
    while stack:
        budget.step()
        current=stack.pop()
        if () in current: continue
        triple=next((r for r in current if len(r)==3),None)
        if triple is None:
            if binary_model(n,current) is not None: return True
        else:
            stack.extend(restrict(current,l) for l in triple)
    return False

def implies(n,left,right,budget):
    return all(not sat(n,left+tuple((-l,) for l in r),budget) for r in right)

@dataclass(frozen=True)
class Program:
    initial: int
    layers: tuple
    def evaluate(self,word):
        s=self.initial
        for v,maps in self.layers: s=(maps[(word>>(v-1))&1]>>s)&1
        return s

def peel(n,rows,budget):
    remaining=list(range(1,n+1))
    peels=[]
    while remaining:
        for v in remaining:
            budget.step()
            fs=(restrict(rows,-v),restrict(rows,v))
            const=[1 if not f else 0 if not sat(n,f,budget) else None for f in fs]
            if any(c is not None for c in const):
                fixed=0 if const[0] is not None else 1
                keep=1-fixed
                maps=[2,2]
                maps[fixed]=3*const[fixed]
            elif implies(n,fs[0],fs[1],budget) and implies(n,fs[1],fs[0],budget):
                keep,maps=0,[2,2]
            else:
                common=tuple(tuple(l for l in r if abs(l)!=v) for r in rows)
                if sat(n,common,budget): continue
                def clash(a,b):
                    budget.step()
                    return any(-l in b for l in a)
                if not all(clash(a,b) for a in fs[0] for b in fs[1]): continue
                keep,maps=0,[2,1]
            rows=fs[keep]
            remaining.remove(v)
            peels.append((v,tuple(maps)))
            break
        else:
            return None
    return Program(int(not rows),tuple(reversed(peels)))

def format_ok(rows,t):
    return all(len(r)<=3 for r in rows) and sum(len(r)==3 for r in rows)<=t

def recognize(n,rows,cap=100000,max_ternary=8):
    rows=normalize(n,rows)
    budget=Budget(cap)
    if not format_ok(rows,max_ternary): return "SKIP_FORMAT",None,0
    try: p=peel(n,rows,budget)
    except Exhausted: return "SKIP_BUDGET",None,budget.used
    return ("RECOGNIZED" if p is not None else "NO_ORDER"),p,budget.used

def reset_cases(program,budget):
    """Disjoint last-reset cases, as signed pins and a required parity."""
    for j in range(-1,len(program.layers)):
        budget.step()
        pins=[]
        rhs=program.initial if j==-1 else 0
        mask=0
        for k,(v,maps) in enumerate(program.layers):
            if k<j: continue
            allowed=[x for x in (0,1) if (maps[x] in (0,3))==(k==j)]
            if not allowed: break
            if len(allowed)==1: pins.append(v if allowed[0] else -v)
            rhs ^= maps[0]&1
            if (maps[0]^maps[1])&1: mask ^=1<<(v-1)
        else:
            yield pins,mask,rhs^1

def accepts(rows,word):
    return all(any(bool(word&(1<<(abs(l)-1)))==(l>0) for l in r) for r in rows)

def parity_model(n,rows,mask,rhs,budget):
    budget.step()
    u=binary_model(n,rows)
    if u is None: return None
    if (u&mask).bit_count()%2==rhs: return u
    graph=[[] for _ in range(n)]
    conflicts=[]
    for r in rows:
        signed=[-l if u&(1<<(abs(l)-1)) else l for l in r]
        neg=[-l-1 for l in signed if l<0]
        pos=[l-1 for l in signed if l>0]
        if pos:
            graph[neg[0]].append(pos[0])
        else:
            conflicts.append(sum(1<<i for i in neg))
    for i in range(n):
        budget.step()
        flip=1<<i
        stack=[i]
        while stack:
            for v in graph[stack.pop()]:
                if not flip&(1<<v):
                    flip |= 1<<v
                    stack.append(v)
        if (mask&flip).bit_count()%2 and all((flip&c)!=c for c in conflicts):
            return u^flip
    return None

def discover(n,rows,*,candidates=(),cap=100000,max_ternary=8):
    """Choose original clause IDs for the two-state factor; leave all others in 2CNF."""
    raw=tuple(tuple(r) for r in rows)
    normalized=[normalize(n,[r]) for r in raw]
    default=tuple(i for i,f in enumerate(normalized) if f and len(f[0])>2)
    budget=Budget(cap)
    from itertools import chain
    try:
        for ids in chain(candidates,[default]):
            budget.step()
            ids=set(ids)
            if any(type(i) is not int or not 0<=i<len(raw) for i in ids): raise ValueError("invalid clause index")
            def subset(flag):
                return normalize(n,(r for i,f in enumerate(normalized) if (i in ids)==flag for r in f))
            inside,outside=subset(True),subset(False)
            if not format_ok(inside,max_ternary) or any(len(r)>2 for r in outside): continue
            program=peel(n,inside,budget)
            if program is None: continue
            for pins,mask,rhs in reset_cases(program,budget):
                word=parity_model(n,outside+tuple((l,) for l in pins),mask,rhs,budget)
                if word is not None:
                    if not accepts(raw,word): raise AssertionError("original CNF witness replay failed")
                    return "SAT",word,budget.used
            return "UNSAT",None,budget.used
    except Exhausted: return "SKIP_BUDGET",None,budget.used
    return "SKIP_FACTOR",None,budget.used

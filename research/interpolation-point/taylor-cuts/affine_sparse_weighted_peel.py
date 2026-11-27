"""Exact nonnegative integer sparse factors on binary linear evaluation scopes."""
from dataclasses import dataclass
from affine_cell_energy import solve,dot
from affine_union_cache import canonical
from clause_rank_drop import _combination
from private_syndrome_elimination import scope_split,row_basis,values


@dataclass
class Factor:
    scope: tuple
    default: int
    entries: dict  # actual exceptional weights

    def value(self,z):
        return self.entries.get(z,self.default)


def normalize(n,f):
    P=row_basis(n,f.scope)
    if len(P)!=len(f.scope):raise ValueError("scope must be independent")
    if type(f.default) is not int or f.default<0:raise ValueError("invalid default")
    entries={}
    for z,w in f.entries.items():
        if type(z) is not int or not 0<=z<1<<len(P) or type(w) is not int or w<0:
            raise ValueError("invalid exception")
        if w!=f.default:
            x,_=solve(n,((a,z>>j&1) for j,a in enumerate(f.scope)))
            entries[values(P,x)]=w
    return Factor(P,f.default,entries)


def multiply(f,g):
    default=f.default*g.default
    entries={}
    for z in f.entries.keys()|g.entries.keys():
        w=f.value(z)*g.value(z)
        if w!=default:entries[z]=w
    return Factor(f.scope,default,entries)


@dataclass
class Step:
    exterior: tuple
    shared: tuple
    private: tuple
    default: int
    exceptions: dict

    def lift(self,n,x):
        table=self.exceptions.get(values(self.shared,x),{})
        if self.default:
            code=0
            while table.get(code,self.default)==0:code+=1
            if code>=1<<len(self.private):raise AssertionError("positive fiber lost")
        else:
            code=next(z for z,w in table.items() if w)
        pins=[(a,dot(a,x)) for a in self.exterior]
        pins.extend((a,code>>j&1) for j,a in enumerate(self.private))
        return solve(n,pins)[0]


@dataclass
class Residual:
    n: int
    scale: int
    scope: tuple
    factors: list
    trace: list
    source_chart: tuple | None = None

    def lift_original(self,x):
        """Lift an externally supplied positive residual word to original coordinates."""
        seed=self.lift(x)
        if self.source_chart is None:return seed
        origin,free,clauses,xors=self.source_chart
        word=origin^_combination(free,seed)
        if not (all(any(bool(word>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
                and all(dot(word,a)==b for a,b in xors)):
            raise AssertionError("incorrect source witness")
        return word

    def lift(self,x):
        if not 0<=x<1<<self.n or not self.scale or not all(f.value(values(f.scope,x)) for f in self.factors):
            raise ValueError("invalid or zero-weight residual word")
        for step in reversed(self.trace):x=step.lift(self.n,x)
        return x

    def finish(self,rank_budget=0):
        if type(rank_budget) is not int or rank_budget<0:raise ValueError("invalid rank budget")
        if not self.scale:return 0,None
        if len(self.scope)>rank_budget:return None,None
        total=0; witness=None
        for z in range(1<<len(self.scope)):
            x,_=solve(self.n,((a,z>>j&1) for j,a in enumerate(self.scope)))
            weight=1
            for f in self.factors:weight*=f.value(values(f.scope,x))
            total+=weight
            if weight and witness is None:witness=self.lift(x)
        return self.scale*total,witness


def reduce_weighted(n,factors):
    if type(n) is not int or n<0:raise ValueError("invalid dimension")
    factors=[normalize(n,f) for f in factors]
    oldrank=n;scale=1;trace=[]
    while True:
        merged={}
        for f in factors:
            merged[f.scope]=multiply(merged[f.scope],f) if f.scope in merged else f
        factors=[]
        for f in merged.values():
            if not f.scope or not f.entries:
                scale*=f.value(0)
            elif len(f.entries)==1<<len(f.scope) and not any(f.entries.values()):
                scale=0
            else:factors.append(f)
        scope=row_basis(n,(a for f in factors for a in f.scope))
        scale <<= oldrank-len(scope)
        if not scale:return Residual(n,0,(),[],[])
        for i,f in enumerate(factors):
            others=factors[:i]+factors[i+1:]
            W=row_basis(n,(a for g in others for a in g.scope))
            L,private,sc,pc=scope_split(n,f.scope,W)
            if not private:continue
            default=f.default<<len(private)
            changes={}; buckets={}
            for z,w in f.entries.items():
                key=values(sc,z); code=values(pc,z)
                changes[key]=changes.get(key,0)+w-f.default
                buckets.setdefault(key,{})[code]=w
            new=Factor(L,default,{z:default+v for z,v in changes.items() if v})
            trace.append(Step(W,L,private,f.default,buckets))
            factors=others+[new]
            oldrank=len(W)  # private dimensions have been explicitly summed
            break
        else:return Residual(n,scale,scope,factors,trace)


def count_cnf(n,clauses,xor_rows=(),*,rank_budget=0):
    """Return total, original witness, residual; missing total denotes a rank cap."""
    if type(n) is not int or n<0:raise ValueError("invalid dimension")
    clauses=tuple(tuple(c) for c in clauses);xor_rows=tuple(xor_rows)
    if any(type(l) is not int or not 1<=abs(l)<=n for c in clauses for l in c):
        raise ValueError("invalid literal")
    chart=solve(n,xor_rows)
    if chart is None:return 0,None,None
    origin,free=chart;d=len(free);terms=[]
    for c in clauses:
        eq=[]
        for l in c:
            a=1<<(abs(l)-1)
            eq.append((values(free,a),int(l<0)^dot(a,origin)))
        flat=canonical(d,eq)
        if flat is None:continue
        P=tuple(a for a,_ in flat)
        z=sum(b<<i for i,(_,b) in enumerate(flat))
        terms.append(Factor(P,1,{z:0}))
    residual=reduce_weighted(d,terms)
    residual.source_chart=(origin,free,clauses,xor_rows)
    total,seed=residual.finish(rank_budget)
    if seed is None:return total,None,residual
    x=origin^_combination(free,seed)
    assert all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
    assert all(dot(x,a)==b for a,b in xor_rows)
    return total,x,residual

"""Affine prefix projection (unbounded resulting parity scopes), joint grouped tail."""
from lift import Basis,Meter,Refused,Answer,grouped,condition,normalize,affine,xor_equations
def projected(n,rows,B,meter):
    private=Basis(); result=Basis()
    # Renumber all private coordinates above boundary coordinates for elimination.
    bm=sum(1<<v for v in B); allmask=(1<<n)-1
    def pack(a): return (a&bm)|((a&(allmask^bm))<<n)
    for scope,bads in grouped(rows).items():
        size=1<<len(scope); meter.charge(size)
        good=[w for w in range(size) if w not in bads]
        if not good: return None
        eq=affine(scope,good)
        if eq is None: raise Refused
        for a,b in eq:
            a=pack(a)
            while a.bit_length()>n:
                i=a.bit_length()-1
                if i not in private.rows:
                    private.rows[i]=(a,b)
                    break
                c,d=private.rows[i]; a^=c; b^=d
            else:
                if not result.add(a,b): return None
    return result
def reduce(a,b,rows):
    for i,(v,u) in sorted(rows.items(),reverse=True):
        if a>>i&1: a^=v; b^=u
    return a,b

def join_affine(n,prefix,tail,boundary,first_pins,second_pins,*,fixed=(),arity=3,cap=1000000):
    if any(type(v)!=int or v<0 for v in (n,cap,arity)): raise ValueError("invalid limit")
    indices=tuple(boundary); frozen=tuple(fixed)
    if any(type(v)!=int or not 1<=v<=n for v in (*indices,*frozen)): raise ValueError("invalid variable ID")
    B={v-1 for v in indices}; left=normalize(n,prefix); tail=normalize(n,tail)
    if ({abs(l)-1 for r in left for l in r}&{abs(l)-1 for r in tail for l in r})-B:
        raise ValueError("unreported shared name")
    pins=[tuple(first_pins),tuple(second_pins)]
    if any(type(l)!=int or not 1<=abs(l)<=n or abs(l)-1 in B for p in pins for l in p):
        raise ValueError("invalid selectors")
    if {abs(l) for l in pins[0]}!={abs(l) for l in pins[1]}: raise ValueError("different prefix selector names")
    meter=Meter(cap)
    def ans(tag,w=None): return Answer(tag,w,("AFFINE","AFFINE"),0,meter.used)
    if any(len(r)>arity for r in (*left,*tail)): return ans("SKIP")
    try:
        A,C=[projected(n,condition(left,p),B,meter) for p in pins]
        if A is None or C is None: return ans("LIFT",0) if A is C else ans("NO_GROUP_LIFT")
        shifts=Basis()
        for v in frozen: shifts.add(1<<(v-1),0)
        for scope,bad in grouped(tail).items(): xor_equations(scope,bad,bad,shifts,meter)
        if len(A.rows)!=len(C.rows): return ans("NO_GROUP_LIFT")
        for a,b in A.rows.values():
            rem,delta=reduce(a,b,C.rows)
            if rem or not shifts.add(a,delta): return ans("NO_GROUP_LIFT")
        return ans("LIFT",shifts.lift())
    except Refused: return ans("SKIP")
def extend_affine(n,prefix,pins,boundary_values):
    raw=normalize(n,prefix); fix=tuple(pins)+tuple(boundary_values)
    if any(type(l)!=int or not 1<=abs(l)<=n for l in fix): raise ValueError("invalid pin")
    eq=projected(n,condition(raw,fix),set(range(n)),Meter(1<<60))
    if eq is None: return None
    for l in fix:
        if not eq.add(1<<(abs(l)-1),int(l>0)): return None
    w=eq.lift()
    if any(not any(bool(w&(1<<(abs(l)-1)))==(l>0) for l in r) for r in raw): raise AssertionError("replay failed")
    return w

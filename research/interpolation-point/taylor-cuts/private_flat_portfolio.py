"""Count-preserving sparse private peel followed by capped exact rank-drop."""
from itertools import product
from affine_cell_energy import dot,solve as linear_solve
from affine_sparse_weighted_peel import count_cnf
from clause_rank_drop_hybrid import count as flat_count


def _compile(R):
    # Work on independent evaluations of the live span, so no fiber correction.
    P=R.scope; refs={}; pins=[]; hard=[]; soft=[]; scale=R.scale
    for f in R.factors:
        ids=[]
        for a in f.scope:
            if a not in refs:
                d,_=linear_solve(len(R.scope),[(sum(((b>>i)&1)<<j for j,b in enumerate(P)),(a>>i)&1)
                                               for i in range(R.n)])
                idx=len(P)+len(refs)
                refs[a]=idx+1
                pins.append((d^(1<<idx),0))
            ids.append(refs[a])
        if f.default>0 and all(w==0 for w in f.entries.values()):
            scale*=f.default
            for z in f.entries:
                hard.append(tuple(-v if z>>j&1 else v for j,v in enumerate(ids)))
        elif f.default==0 and len(f.entries)==1:
            z,w=next(iter(f.entries.items()))
            scale*=w
            pins.extend((1<<(v-1),(z>>j)&1) for j,v in enumerate(ids))
        else:
            choices=[]
            if f.default:choices.append((f.default,()))
            for z,w in f.entries.items():
                choices.append((w-f.default,tuple((1<<(v-1),(z>>j)&1) for j,v in enumerate(ids))))
            soft.append(choices)
    return len(P)+len(refs),pins,hard,soft,scale


def solve(n,clauses,xor_rows=(),*,peel_rank_cap=0,flat_cap=0,soft_terms_cap=1,source_flat_cap=None):
    """status SAT/UNSAT implies an exact count; UNKNOWN means a cap was exceeded."""
    if any(type(c) is not int or c<0 for c in (peel_rank_cap,flat_cap,soft_terms_cap)):
        raise ValueError("invalid cap")
    if source_flat_cap is not None and (type(source_flat_cap) is not int or source_flat_cap<0):
        raise ValueError("invalid source fallback cap")
    cs=tuple(tuple(c) for c in clauses); rs=tuple(xor_rows)
    metrics={"flat_calls":0,"peel_rank_cap":peel_rank_cap,"flat_cap":flat_cap,
             "soft_terms_cap":soft_terms_cap,"source_flat_cap":source_flat_cap}
    def result(stage,count,w):
        if count is not None:
            if count<0 or (w is None)!=(count==0):raise AssertionError("invalid exact result")
            if w is not None and not(all(any(bool(w>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs)
                                     and all(dot(w,m)==b for m,b in rs)):
                raise AssertionError("original witness failed")
        return dict(stage=stage,status="UNKNOWN" if count is None else "SAT" if count else "UNSAT",
                    count=count,witness=w,metrics=metrics)
    count,w,R=count_cnf(n,cs,rs,rank_budget=peel_rank_cap)
    if R is not None:metrics.update(peel_steps=len(R.trace),residual_rank=len(R.scope),scale=R.scale)
    if count is not None:return result("private",count,w)
    d,pins,hard,soft,scale=_compile(R)
    terms=1
    for choices in soft:terms*=len(choices)
    metrics["soft_terms"]=terms
    def mass(prefix):
        total=0
        for choice in product(*soft):
            weight=scale;extra=[]
            for c,eq in choice:
                weight*=c;extra.extend(eq)
            metrics["flat_calls"]+=1
            v,_,_=flat_count(d,hard,(*pins,*extra,*prefix),cap=flat_cap,group_equal=True)
            if v is None:return None
            total+=v*weight
        if total<0:raise AssertionError("negative mass")
        return total
    if terms<=soft_terms_cap:
        count=mass(())
        if count==0:return result("private-flat",0,None)
        if count is not None:
            prefix=[]; z=0
            for i in range(len(R.scope)):
                a=1<<i
                left=mass((*prefix,(a,0)))
                if left is None:raise AssertionError("new pins increased rank-drop optimum")
                bit=int(left==0);prefix.append((a,bit));z|=bit<<i
            seed,_=linear_solve(R.n,[(a,(z>>j)&1) for j,a in enumerate(R.scope)])
            return result("private-flat",count,R.lift_original(seed))
    if source_flat_cap is not None:
        metrics["flat_calls"]+=1
        count,w,_=flat_count(n,cs,rs,cap=source_flat_cap,group_equal=True)
        if count is not None:return result("source-flat",count,w)
    return result("caps",None,None)

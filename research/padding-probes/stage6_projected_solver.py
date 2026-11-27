"""EQ-propagated positive projection and full coalesced physical source portfolio."""
from collections.abc import Mapping
from importlib import import_module
from stack_alias import decode_alias
from stage6_positive_projection import aliases as projected_aliases, solve_positive
from stage6_source_solver import compile_source, fixed_dfa, _satisfies, _MODULES, _DEFAULTS


def solve(n,clauses,*,exact_twice=False,source_pins=(),stages=None,fallback_limit=0):
    """Normalize every dummy ID, preserving positive feasibility and the zero anchor."""
    job=compile_source(n,clauses,exact_twice=exact_twice)
    if fallback_limit is not None and (type(fallback_limit) is not int or fallback_limit<0):
        raise ValueError("invalid fallback assignment limit")
    fixed={}
    conflict=False
    for v,b in (source_pins.items() if isinstance(source_pins,Mapping) else source_pins):
        if type(v) is not int or not 1<=v<=n or type(b) is not int or b not in (0,1):
            raise ValueError("invalid original pin")
        conflict |= fixed.setdefault(v,b)!=b
    attempts=[]
    def result(status,witness=None,physical=None,**extra):
        sparse=None if witness is None else tuple(sorted(v for v in set(job.anchors)|set(fixed)
                                                     if v<=n and (witness>>(v-1))&1))
        return dict(status=status,witness=witness,sparse_witness=sparse,physical=physical,
                    dummy_pins=len(job.dummy_bits),attempts=attempts,**extra)
    if conflict:
        return result("UNSAT",reason="contradictory source pins")
    table,initial,bottom,outputs=fixed_dfa()
    collapsed=projected_aliases(job)
    def verified(raw):
        state=initial
        for byte in raw:
            state=table[state,bottom,byte][0]
        if outputs[state]!=1:
            raise ArithmeticError("original physical predictor rejected alleged SAT word")
        decode_alias(raw,collapsed)
        _,_,_,underlying=decode_alias(raw,job.aliases)
        if any(underlying[k]!=b for k,b in job.dummy_bits.items()):
            raise ArithmeticError("physical witness violates normalized dummy chart")
        mask=job.lift(raw)
        for v,b in fixed.items():
            if v not in job.anchors and b:
                mask|=1<<(v-1)
        if (not _satisfies(job.clauses,mask) or
            any((mask>>(v-1)&1)!=b for v,b in fixed.items())):
            raise ArithmeticError("original CNF or pin mismatch")
        return result("SAT",mask,raw)
    pins=tuple((job.anchors[v],b) for v,b in fixed.items() if v in job.anchors)
    pins+=tuple(job.dummy_bits.items())
    if stages is None:
        stages=("projected_gaussian","projected_compressed","projected_rank2","block")
    for item in stages:
        name,options=(item,{}) if isinstance(item,str) else item
        projected_defaults={"projected_gaussian":{"exception_cap":8,"branch_cap":256},
                           "projected_compressed":{"omission_cap":12,"state_cap":128,"work_cap":2048},
                           "projected_rank2":{"omission_cap":12,"codimension_cap":8}}
        if name in projected_defaults:
            options=dict(options)
            if set(options)-projected_defaults[name].keys():
                raise ValueError("unsupported projected stage option")
            status,mask,decision=solve_positive(job,fixed,name,{**projected_defaults[name],**options})
            attempts.append(dict(stage=name,status=decision["status"],metrics=decision["metrics"],
                                 reason=decision.get("reason")))
            if status=="SAT":
                return verified(job.word(mask))
            if status=="UNSAT":
                return result("UNSAT",reason="exact positive projection empty")
            continue
        if name not in _MODULES:
            raise ValueError("unknown source stage")
        options=dict(options)
        allowed=set(_DEFAULTS[name])|{"backend","codebooks"}
        if name=="flat":
            allowed.add("max_flat_rank")
        if name=="block":
            allowed.discard("codebooks")
        if set(options)-allowed:
            raise ValueError("unsupported physical stage option")
        options={**_DEFAULTS[name],**options}
        physical=import_module(_MODULES[name]).solve([],job.slots_n,collapsed,table,initial,
                     bottom,outputs,id_pins=pins,schedule={},**options)
        status=physical["status"]
        attempts.append(dict(stage=name,status=status,metrics=physical["metrics"],
                             reason=physical.get("reason")))
        for sample in physical["samples"]:
            if sample["prediction"]==1:
                return verified(sample["physical"])
        if status=="constant" and physical.get("value")==0:
            return result("UNSAT",reason="complete physical negative")
        if status!="unknown":
            raise ArithmeticError("physical stage lost its guaranteed zero anchor or positive witness")
    active=[v for v in job.anchors if v<=n and v not in fixed]
    base=sum(b<<(v-1) for v,b in fixed.items())
    total=1<<len(active)
    limit=total if fallback_limit is None else min(total,fallback_limit)
    for i in range(limit):
        mask=base|sum(((i>>j)&1)<<(v-1) for j,v in enumerate(active))
        if _satisfies(job.clauses,mask):
            attempts.append(dict(stage="source-enumeration",examined=i+1,total=total))
            return verified(job.word(mask))
    attempts.append(dict(stage="source-enumeration",examined=limit,total=total))
    return result("UNSAT" if limit==total else "UNKNOWN",
                  reason="source search complete" if limit==total else "source assignment cap")

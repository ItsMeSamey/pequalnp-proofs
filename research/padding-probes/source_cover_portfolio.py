"""Sparse original 3-CNF portfolio with independently replayed physical witnesses."""
from collections.abc import Mapping
from source_easy_prepass import solve_prepass
from source_cover_sat import solve_dense
from stage6_source_solver import compile_source, fixed_dfa
from stage6_projected_solver import solve as solve_projected
from stack_alias import decode_alias


def solve(n,clauses,*,source_pins=(),exact_twice=False,stages=None,prepass=True,node_cap=None):
    """Return SAT, UNSAT, or UNKNOWN. Variables absent from true_variables are false."""
    if type(n) is not int or n<0 or type(prepass) is not bool or type(exact_twice) is not bool:
        raise ValueError("invalid source parameters")
    if node_cap is not None and (type(node_cap) is not int or node_cap<0):
        raise ValueError("invalid cover node cap")
    rows=tuple(tuple(row) for row in clauses)
    if any(len(row)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in row) for row in rows):
        raise ValueError("invalid source clause")
    pins=tuple(source_pins.items() if isinstance(source_pins,Mapping) else source_pins)
    if any(type(v) is not int or not 1<=v<=n or type(b) is not int or b not in (0,1)
           for v,b in pins):
        raise ValueError("invalid original pin")
    names=sorted({abs(l) for row in rows for l in row}|{v for v,_ in pins})
    index={v:i+1 for i,v in enumerate(names)}
    dense=tuple(tuple(index[abs(l)] if l>0 else -index[-l] for l in row) for row in rows)
    dense_pins=tuple((index[v],b) for v,b in pins)
    d=len(names)
    attempts=[]

    def finish(status,route,word=None,raw=None):
        answer=dict(status=status,route=route,attempts=attempts,true_variables=None,physical=None)
        if status!="SAT":
            if status not in ("UNSAT","UNKNOWN"):
                raise ArithmeticError("invalid route status")
            return answer
        if type(word) is not int or word<0 or word.bit_length()>d:
            raise ArithmeticError("invalid dense assignment")
        true=tuple(v for j,v in enumerate(names) if word>>j&1)
        chosen=set(true)
        if (any(not any((abs(l) in chosen)==(l>0) for l in row) for row in rows)
                or any(int(v in chosen)!=b for v,b in pins)):
            raise ArithmeticError("invalid original assignment or pins")
        job=compile_source(d,dense,exact_twice=exact_twice)
        if raw is None:
            raw=job.word(word)
        lifted=job.lift(raw)
        active_mask=sum(1<<(v-1) for v in job.anchors if v<=d)
        if lifted!=(word&active_mask):
            raise ArithmeticError("original occurrence projection mismatch")
        _,_,_,underlying=decode_alias(raw,job.aliases)
        if any(underlying[k]!=v for k,v in job.dummy_bits.items()):
            raise ArithmeticError("dummy normalization mismatch")
        table,state,bottom,outputs=fixed_dfa()
        for byte in raw:
            state=table[state,bottom,byte][0]
        if outputs[state]!=1:
            raise ArithmeticError("fixed physical machine rejected witness")
        return dict(answer,true_variables=true,physical=raw)

    if prepass:
        status,word,method=solve_prepass(d,dense,pins=dense_pins)
        attempts.append(dict(route="prepass",status=status,method=method))
        if status!="UNKNOWN":
            return finish(status,"prepass",word)
    middle=solve_projected(d,dense,source_pins=dense_pins,exact_twice=exact_twice,
                           stages=stages,fallback_limit=0)
    attempts.append(dict(route="projected",status=middle["status"],attempts=middle["attempts"]))
    if middle["status"]!="UNKNOWN":
        return finish(middle["status"],"projected",middle["witness"],middle["physical"])
    last=solve_dense(d,dense,pins=dense_pins,node_cap=node_cap)
    attempts.append(dict(route="cover",status=last["status"],metrics=last["metrics"]))
    return finish(last["status"],"cover",last["witness"])

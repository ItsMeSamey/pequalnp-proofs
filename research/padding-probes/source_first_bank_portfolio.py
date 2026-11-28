"""Source-first signed NAND banks with cover-budgeted pair discovery."""
from collections.abc import Mapping
from interval_optimizer import minimum_partition
from corridor_nand import corridor_witness
from source_nand_compile import lift
from source_nand_portfolio import _cover_bound
from source_chart_cover_portfolio import solve as fallback
from source_cover_portfolio import solve as physical_replay


def solve(n,clauses,*,source_pins=(),exact_twice=False,stages=None,prepass=True,
          node_cap=None,nand_branch_cap=None,pair_node_cap=None,partition_gate_cap=128):
    """NAND cap bounds full binary branches; node_cap bounds fallback cover nodes."""
    from source_bank_nand import compile_source
    if type(n) is not int or n<0 or type(exact_twice) is not bool or type(prepass) is not bool:
        raise ValueError("invalid source parameters")
    for cap in (node_cap,nand_branch_cap,pair_node_cap,partition_gate_cap):
        if cap is not None and (type(cap) is not int or cap<0):
            raise ValueError("invalid search budget")
    rows=tuple(tuple(c) for c in clauses)
    if any(len(c)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in c) for c in rows):
        raise ValueError("invalid source clause")
    pins=tuple(tuple(p) for p in (source_pins.items() if isinstance(source_pins,Mapping) else source_pins))
    if any(len(p)!=2 or type(p[0]) is not int or not 1<=p[0]<=n or type(p[1]) is not int
           or p[1] not in (0,1) for p in pins):
        raise ValueError("invalid source pin")
    front=fallback(n,rows,source_pins=pins,exact_twice=exact_twice,stages=stages,
                   prepass=prepass,node_cap=0)
    if front["status"]!="UNKNOWN":
        return front
    v,ceiling=_cover_bound(rows,dict(pins))
    discovery_cap=ceiling if pair_node_cap is None else min(pair_node_cap,ceiling)
    job=compile_source(n,rows,pins=pins,pair_node_cap=discovery_cap)
    metrics=dict(inputs=job["inputs"],gates=len(job["gates"]),bad_blocks=None,
                 branch_bound=None,cover_bound=None,intervals=(),dispatched=False)
    metrics.update(pair_count=job.get("pair_count",0),pair_search=job["pair_search"],optimizer_used=False,
                   exterior_rows=len(job.get("clauses",())))
    metrics.update(discovery_cap=discovery_cap,cover_bound=ceiling,cover_variables=v)
    attempts=list(front["attempts"])
    def finish(status,route,raw=None):
        attempts.append(dict(route=route,status=status,metrics=metrics))
        if status=="UNSAT":
            return dict(status=status,route=route,attempts=attempts,true_variables=None,physical=None)
        wires=list(raw)
        for a,b in job["gates"]:
            wires.append(1^(wires[a]&wires[b]))
        if any(not any(wires[abs(l)-1]==int(l>0) for l in c) for c in job["clauses"]):
            raise ArithmeticError("mixed exterior replay failed")
        names=tuple(lift(job,raw))
        used={abs(l) for c in rows for l in c}|{v for v,_ in pins}
        selected=set(names)
        if (names!=tuple(sorted(selected)) or not selected<=used or
                any(not any((abs(l) in selected)==(l>0) for l in c) for c in rows) or
                any(int(v in selected)!=b for v,b in pins)):
            raise ArithmeticError("NAND witness fails original source")
        held=tuple((v,int(v in selected)) for v in sorted(used))
        replay=physical_replay(n,rows,source_pins=held,exact_twice=exact_twice,prepass=True,
                               stages=(),node_cap=0)
        if replay["status"]!="SAT" or replay["true_variables"]!=names or type(replay["physical"]) is not bytes:
            raise ArithmeticError("fully pinned physical replay failed")
        attempts.append(dict(route="pinned-replay",status="SAT",attempts=replay["attempts"]))
        return dict(status="SAT",route=route,attempts=attempts,true_variables=names,
                    physical=replay["physical"])
    if job["status"] in ("SAT","UNSAT"):
        return finish(job["status"],"bank-constant",())
    if job["status"]!="ok":
        raise ArithmeticError("unexpected compiler status")
    inputs,gates=job["inputs"],job["gates"]
    if partition_gate_cap is None or len(gates)<=partition_gate_cap:
        bad,intervals=minimum_partition(inputs,gates,job["observed"])
        metrics["optimizer_used"]=True
    else:
        intervals=job["banks"]
        bad=len(intervals)
    if bad>job["pair_count"]:
        raise ArithmeticError("optimizer exceeded bank bound")
    branches=1<<bad
    metrics.update(bad_blocks=bad,intervals=intervals,branch_bound=branches,
                   cover_bound=ceiling,cover_variables=v)
    if branches<=ceiling and (nand_branch_cap is None or branches<=nand_branch_cap):
        metrics["dispatched"]=True
        groups=tuple(range(start,stop) for start,stop in intervals)
        status,raw=corridor_witness(inputs,gates,groups,clauses=job["clauses"],max_bad=bad)
        if status=="sat":
            return finish("SAT","bank-nand",raw)
        if status=="unsat":
            return finish("UNSAT","bank-nand")
        if status!="skip":
            raise ArithmeticError("unexpected NAND solver status")
        reason="backend skip"
    else:
        reason="NAND branch cap" if nand_branch_cap is not None and branches>nand_branch_cap else "cover clock"
    attempts.append(dict(route="bank-nand",status="UNKNOWN",reason=reason,metrics=metrics))
    answer=fallback(n,rows,source_pins=pins,exact_twice=exact_twice,stages=(),
                             prepass=False,node_cap=node_cap)
    return dict(answer,attempts=[*attempts,*answer["attempts"]])

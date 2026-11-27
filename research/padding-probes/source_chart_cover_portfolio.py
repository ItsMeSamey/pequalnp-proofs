"""Sparse affine-chart recognition followed, when needed, by the frozen source solver."""
from collections.abc import Mapping
from ring_image_affine_hull_sparse import solve_source_sparse
from source_cover_portfolio import solve as solve_stage7


def solve(n,clauses,*,source_pins=(),exact_twice=False,stages=None,prepass=True,node_cap=None):
    """Return original true IDs and verified physical bytes on SAT.

    Supply the sibling pnp-general-separation and compression directories on
    the normal module search path in addition to physical-bdd-union.
    """
    if type(n) is not int or n<0 or type(exact_twice) is not bool or type(prepass) is not bool:
        raise ValueError("invalid source parameters")
    if node_cap is not None and (type(node_cap) is not int or node_cap<0):
        raise ValueError("invalid cover node cap")
    rows=tuple(tuple(c) for c in clauses)
    if any(len(c)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in c) for c in rows):
        raise ValueError("invalid source clause")
    pins=tuple(tuple(p) for p in (source_pins.items() if isinstance(source_pins,Mapping) else source_pins))
    if any(len(p)!=2 or type(p[0]) is not int or not 1<=p[0]<=n or type(p[1]) is not int
           or p[1] not in (0,1) for p in pins):
        raise ValueError("invalid source pin")
    pinned_rows=tuple((v if b else -v,) for v,b in pins)
    chart=solve_source_sparse(n,rows+pinned_rows)
    status=chart["status"]
    attempt=dict(route="chart",status=status,reason=chart.get("reason"))
    if status=="zero":
        return dict(status="UNSAT",route="chart",true_variables=None,physical=None,attempts=[attempt])
    if status=="unknown":
        answer=solve_stage7(n,rows,source_pins=pins,exact_twice=exact_twice,
                            stages=stages,prepass=prepass,node_cap=node_cap)
        return dict(answer,attempts=[attempt,*answer["attempts"]])
    if status!="nonzero":
        raise ArithmeticError("unexpected chart status")
    ids=tuple(chart["true_ids"])
    used={abs(l) for row in rows for l in row}|{v for v,_ in pins}
    if any(type(v) is not int or v not in used for v in ids) or ids!=tuple(sorted(set(ids))):
        raise ArithmeticError("invalid sparse chart witness")
    selected=set(ids)
    if (any(not any((abs(l) in selected)==(l>0) for l in row) for row in rows) or
            any(int(v in selected)!=b for v,b in pins)):
        raise ArithmeticError("chart witness violates original clauses or pins")
    enlarged=tuple((v,int(v in selected)) for v in sorted(used))
    replay=solve_stage7(n,rows,source_pins=enlarged,exact_twice=exact_twice,
                        stages=(),prepass=True,node_cap=0)
    if (replay["status"]!="SAT" or replay["true_variables"]!=ids or
            not isinstance(replay["physical"],bytes)):
        raise ArithmeticError("fully pinned original physical replay failed")
    return dict(status="SAT",route="chart",true_variables=ids,physical=replay["physical"],
                attempts=[attempt,dict(route="pinned-replay",status="SAT",attempts=replay["attempts"])])

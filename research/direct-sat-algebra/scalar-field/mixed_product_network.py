"""One raw quadratic bit over a direct product of recognized field-network fibers."""
from dataclasses import dataclass
from itertools import combinations
from centroid_fiber import coordinate_map
from hidden_product_network import recover
from product_network_witness import witness
from quadratic_centroid import decompose, zero_combinations
from quadratic_image import Quadratic, evaluate, normalize, parity
from quadratic_target import apply_basis, evaluate_anf, interpolate


@dataclass(frozen=True)
class Result:
    status: str
    witness: int | None
    degrees: tuple
    changed_blocks: int | None = None


def scalar_form(function,dim):
    c,l,p = interpolate(function,dim)
    return Quadratic(c,sum(bit << j for j,bit in enumerate(l)),tuple(p))


def solve(n,m,constant,linear,pairs,target,form,required=1):
    """Recognize every centroid block, then search its Cartesian target fiber."""
    if not 0<=target<1<<m or required not in (0,1):
        raise ValueError("invalid target or required bit")
    normalize(n,form)
    try:
        blocks = decompose(n,m,constant,linear,pairs).blocks
    except ValueError as error:
        if str(error).startswith("requires "):
            return Result("UNKNOWN",None,())
        raise
    goal = coordinate_map([v for _,out in blocks for v in out])(target ^ constant)
    local = []
    for domain,out in blocks:
        encode = coordinate_map(out)
        c,l,p = interpolate(lambda v: encode(evaluate_anf(
            0,linear,pairs,apply_basis(domain,v))),len(domain))
        chart = recover(len(domain),len(out),c,l,p)
        if chart is None:
            return Result("UNKNOWN",None,())
        local.append((domain,chart,goal & ((1<<len(out))-1)))
        goal >>= len(out)
    degrees = tuple(chart.field.m for _,chart,_ in local)

    def side(raw):
        return evaluate((form,),raw)

    def found(raw,changes):
        if evaluate_anf(constant,linear,pairs,raw)!=target or side(raw)!=required:
            raise ArithmeticError("original witness verification failed")
        return Result("SAT",raw,degrees,changes)

    roots = []
    baseline = 0
    for domain,chart,subtarget in local:
        root = witness(chart,subtarget,Quadratic(1),1)
        if root is None:
            return Result("UNSAT",None,degrees)
        baseline ^= apply_basis(domain,root)
        roots.append(root)
    if side(baseline)==required:
        return found(baseline,0)

    for (domain,chart,subtarget),root in zip(local,roots):
        outside = baseline ^ apply_basis(domain,root)
        restricted = scalar_form(lambda v: side(outside ^ apply_basis(domain,v)),len(domain))
        model = witness(chart,subtarget,restricted,required)
        if model is not None:
            return found(outside ^ apply_basis(domain,model),1)

    direction_sets = []
    for (domain,chart,subtarget),root in zip(local,roots):
        local_diffs = []
        unit = [1<<j for j in range(len(domain))]
        while True:
            normals = zero_combinations(unit, lambda a: sum(
                parity(a & d)<<j for j,d in enumerate(local_diffs)))
            for a in normals:
                model = witness(chart,subtarget,Quadratic(linear=a),1^parity(a & root))
                if model is not None:
                    local_diffs.append(model ^ root)
                    break
            else:
                break
        direction_sets.append([apply_basis(domain,d) for d in local_diffs])
    for left,right in combinations(direction_sets,2):
        for u in left:
            for v in right:
                if side(baseline ^ u ^ v)==required:
                    return found(baseline ^ u ^ v,2)
    return Result("UNSAT",None,degrees)

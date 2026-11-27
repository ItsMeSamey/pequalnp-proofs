"""Enforce unary domains once; check pair hulls only on valid endpoints."""
from affine_relation import affine_hull
from event_field_codes import relative_hull
from event_affine_compile import compile_factors as compile_unary


def compile_factors(domains,constraints,output,*,codebooks=None,omission_cap=None):
    compiled = compile_unary(domains,(),output,codebooks=codebooks,omission_cap=omission_cap)
    if compiled["status"] != "ok":
        return compiled
    enc = compiled["enc"]
    widths = compiled["widths"]
    offsets = compiled["offset"]
    metrics = compiled["metrics"]
    metrics.update(endpoint_candidates=0, relative_holes=0, relative_affine_relations=0)
    equations = list(compiled["equations"])
    forbidden = set(compiled["cylinders"])
    relations = []
    for u,v,allowed in constraints:
        if u not in enc or v not in enc:
            raise ValueError("constraint on unknown variable")
        pairs = frozenset((x,y) for x,y in allowed if x in enc[u] and y in enc[v])
        relations.append((u,v,pairs))
        metrics["factors"] += 1
        if u == v:
            permitted = {enc[u][x] for x,y in pairs if x==y}
            if not permitted:
                return dict(status="empty",metrics=metrics)
            width = widths[u]
            hull,_ = affine_hull(permitted,width)
            holes = [w for w in enc[u].values() if w not in permitted and
                     all((w&m).bit_count()%2==b for m,b in hull)]
            metrics["endpoint_candidates"] += len(enc[u])
            def scatter(word):
                return word << offsets[u]
        else:
            cut = widths[u]
            width = cut + widths[v]
            low = (1<<cut)-1
            result = relative_hull(enc[u].values(),enc[v].values(),
                                   ((enc[u][x],enc[v][y]) for x,y in pairs),cut,widths[v])
            if result is None:
                return dict(status="empty",metrics=metrics)
            hull,_,holes = result
            metrics["endpoint_candidates"] += len(enc[u])*len(enc[v])
            def scatter(word):
                return ((word & low) << offsets[u]) | ((word >> cut) << offsets[v])
        equations.extend((scatter(m),b) for m,b in hull)
        metrics["relative_holes"] += len(holes)
        metrics["exception_count"] += len(holes)
        metrics["nonaffine_factors"] += int(bool(holes))
        metrics["relative_affine_relations"] += int(not holes)
        if omission_cap is not None and metrics["exception_count"] > omission_cap:
            return dict(status="unknown",reason="omission cap",metrics=metrics)
        mask = scatter((1<<width)-1)
        forbidden.update((mask,scatter(word)) for word in holes)
    metrics["equations"] = len(equations)
    compiled.update(equations=tuple(equations), cylinders=tuple(sorted(forbidden)),relations=relations)
    return compiled

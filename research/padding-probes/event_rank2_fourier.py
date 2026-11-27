"""Exact counts of event records via private flag pairs on projected flats."""
from event_affine_compile import compile_factors
from event_affine_flat import prepare, lift
from projected_rank2_fourier import count_witness


def solve(domains, constraints, output, *, codebooks=None, omission_cap=None, codimension_cap=None):
    if codimension_cap is not None and (type(codimension_cap) is not int or codimension_cap < 0):
        raise ValueError("invalid codimension cap")
    data = compile_factors(domains, constraints, output, codebooks=codebooks, omission_cap=omission_cap)
    counts = {0: 0, 1: 0}
    witnesses = {}
    metrics = data["metrics"]
    metrics["queries"] = {}

    def result(status, **fields):
        if status != "unknown":
            fields["counts"] = counts
        return dict(status=status, witnesses=witnesses, metrics=metrics, **fields)

    if data["status"] != "ok":
        return result(data["status"], **({"reason": data["reason"]} if "reason" in data else {}))
    enc, dec, offset, widths = (data[key] for key in ("enc", "dec", "offset", "widths"))
    unknown = None
    for bit in (0, 1):
        if bit not in enc[output]:
            continue
        value = enc[output][bit]
        pins = tuple((1 << (offset[output]+j), (value >> j) & 1) for j in range(widths[output]))
        chart = prepare(data["width"], data["equations"]+pins, data["cylinders"])
        info = chart["metrics"].copy()
        metrics["queries"][bit] = info
        if chart["status"] == "unsat":
            continue
        if chart["status"] != "ok":
            raise ArithmeticError("unexpected projection status")
        if any(len(flat) != 2 for flat in chart["flats"]):
            unknown = "projected rank exceeds two"
            continue
        d = chart["dimension"]
        count, seed, stats = count_witness(d, chart["flats"], codimension_cap=codimension_cap)
        info.update(stats)
        if count is None:
            unknown = "syndrome codimension cap"
            continue
        free = data["width"] - len(chart["seed"]) - d
        info["ambient_fiber_dimension"] = free
        counts[bit] = count << free
        if seed is None:
            continue
        word = lift(chart, seed)
        witness = {v: dec[v][(word >> offset[v]) & ((1 << widths[v])-1)] for v in enc}
        if witness[output] != bit or any((witness[u], witness[v]) not in pairs
                                         for u, v, pairs in data["relations"]):
            raise ArithmeticError("invalid original record witness")
        witnesses[bit] = witness
    if unknown:
        return result("unknown", reason=unknown)
    if len(witnesses) == 1:
        return result("constant", value=next(iter(witnesses)))
    return result("pair" if witnesses else "empty")

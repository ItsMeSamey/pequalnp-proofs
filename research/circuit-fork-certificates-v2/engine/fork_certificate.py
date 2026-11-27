"""Finite first-branch certificate verification on scalar Boolean care tables."""

import hashlib, itertools, json
from functools import lru_cache
from itertools import combinations


def require(value, message):
    if not value:
        raise ValueError(message)


def derive_edges(care, bits, outside, cert):
    general = set()
    positive = set()
    for stated, pairs in cert["general"].items():
        union = 0
        parities = []
        for x, j, y, k in pairs:
            require(
                j in bits and k in bits and not x & (1 << j) and not y & (1 << k),
                "edge base",
            )
            require(
                care[x] != care[x | 1 << j] and care[y] != care[y | 1 << k],
                "edge labels",
            )
            union |= (x ^ y) | (1 << j) | (1 << k)
            parities.append((sorted((j, k)), care[x] ^ care[y]))
        require(union == int(stated) and not union & outside, "general hyperedge")
        if len(parities) == 1:
            (j, k), value = parities[0]
            require(j == k and value, "same coordinate conflict")
        else:
            require(
                len(parities) == 2
                and parities[0][0] == parities[1][0]
                and parities[0][1] != parities[1][1],
                "relative orientation conflict",
            )
        general.add(union)
    for stated, (a, b, c, d) in cert["monotone"].items():
        union = (a | b | c | d) ^ (a & b & c & d)
        require(not union & outside and union == int(stated), "positive hyperedge")
        require(
            a & b == a
            and c & d == c
            and [care[x] for x in (a, b, c, d)] == [0, 1, 1, 0],
            "positive witnesses",
        )
        positive.add(union)
    # Recompute the corner constraints directly; records of the discovery run are unnecessary.
    for j, k in combinations(bits, 2):
        e = (1 << j) | (1 << k)
        fibers = {}
        for p, label in care.items():
            idx = ((p >> j) & 1) + 2 * ((p >> k) & 1)
            want, avoid = fibers.get(p & ~e, (0, 0))
            fibers[p & ~e] = (want | (label << idx), avoid | ((1 - label) << idx))
        corners = set(range(4))
        for want, avoid in fibers.values():
            fits = lambda table: (table & want) == want and not table & avoid
            if any(fits(z) for z in (0, 15, 3, 12, 5, 10)):
                continue
            corners = {q for q in corners if fits(1 << q) or fits(15 ^ (1 << q))}
        if not corners:
            general.add(e)
        if not corners & {0, 3}:
            positive.add(e)
    return general, positive


def partitions(bits, positive, general, np, ns):
    families = [positive] * np + [general] * ns
    order = sorted(
        bits,
        key=lambda j: -sum(
            1 / e.bit_count() for f in families for e in f if e & (1 << j)
        ),
    )
    incident = [{j: [e for e in f if e & (1 << j)] for j in bits} for f in families]

    def visit(i, groups):
        if i == len(order):
            yield groups
            return
        j = order[i]
        for k, g in enumerate(groups):
            if not g and 0 in groups[(0 if k < np else np) : k]:
                continue
            new = g | 1 << j
            if all(new & e != e for e in incident[k][j]):
                yield from visit(i + 1, groups[:k] + (new,) + groups[k + 1 :])

    yield from visit(0, (0,) * (np + ns))


def consistent(disequalities, flip):
    # Index each signed point with an even literal and use xor 1 as complementation.
    vals = sorted({v ^ flip for pair in disequalities for v in pair})
    ids = {v: 2 * i for i, v in enumerate(vals)}
    n = 2 * len(vals)
    reach = [1 << i for i in range(n)]

    def imply(a, b):
        reach[a] |= 1 << b
        reach[b ^ 1] |= 1 << (a ^ 1)

    for a, b in combinations(vals, 2):
        if a & b == a:
            imply(ids[a], ids[b])
    for a, b in disequalities:
        x, y = ids[a ^ flip], ids[b ^ flip]
        imply(x, y ^ 1)
        imply(x ^ 1, y)
    for k in range(n):
        for i in range(n):
            if reach[i] & (1 << k):
                reach[i] |= reach[k]
    return not any(
        reach[i] & (1 << (i + 1)) and reach[i + 1] & (1 << i) for i in range(0, n, 2)
    )


def minimal(e):
    out = {}
    for mask in sorted(e, key=int.bit_count):
        if not any(old & mask == old for old in out):
            out[mask] = e[mask]
    return out


def orientation_witnesses(care, binate, u):
    obs = [
        (p, j, t)
        for j in binate
        for p, t in care.items()
        if not p >> j & 1 and care.get(p | 1 << j) == 1 - t
    ]
    req = {}
    for (a, j, p), (b, k, q) in itertools.combinations(obs, 2):
        if (a ^ b) & u:
            continue
        req.setdefault((min(j, k), max(j, k), p ^ q), {})[
            (a ^ b) | (1 << j) | (1 << k)
        ] = (a, j, b, k)
    req = {k: minimal(v) for k, v in req.items()}
    gen = {}
    for (j, k, par), d in req.items():
        if j == k and par:
            for m, a in d.items():
                gen[m] = [a]
        if j < k and not par:
            for m, a in d.items():
                for n_, b in req.get((j, k, 1), {}).items():
                    gen[m | n_] = [a, b]
    mon = {}
    for cx in {p & u for p in care}:
        pts = [p for p in care if p & u == cx]
        pos = [p for p in pts if care[p]]
        neg = [p for p in pts if not care[p]]
        up = [(a, b) for a in neg for b in pos if a & b == a]
        dn = [(c, d) for c in pos for d in neg if c & d == c]
        for a, b in up:
            for c, d in dn:
                mon[(a | b | c | d) ^ (a & b & c & d)] = (a, b, c, d)
    return {"general": minimal(gen), "monotone": minimal(mon)}


def prepare(care, feature_count, model):
    require(type(feature_count) is int and feature_count >= 0, "invalid feature count")
    require(
        isinstance(model, dict) and set(model) == {"literals", "fixed_cost"},
        "source model keys",
    )
    literals = model["literals"]
    require(
        isinstance(literals, (list, tuple)) and len(literals) == feature_count,
        "source polarities",
    )
    require(
        all(v in ("positive", "negative", "both_live") for v in literals),
        "unknown source polarity",
    )
    require(
        type(model["fixed_cost"]) is int and model["fixed_cost"] >= 0,
        "invalid fixed cost",
    )
    source = {}
    rows = care.items() if isinstance(care, dict) else care
    for p, t in rows:
        require(type(p) is int and 0 <= p < 1 << feature_count, "invalid care pattern")
        require(type(t) is int and t in (0, 1), "invalid care label")
        require(p not in source, "duplicate care pattern")
        source[p] = t
    require(source, "empty care")
    packed = [
        feature_count,
        list(literals),
        model["fixed_cost"],
        sorted(source.items()),
    ]
    digest = hashlib.sha256(
        json.dumps(packed, separators=(",", ":")).encode()
    ).hexdigest()
    flip = sum(1 << i for i, v in enumerate(literals) if v == "negative")
    both = sum(1 << i for i, v in enumerate(literals) if v == "both_live")
    table = {p ^ flip: t for p, t in source.items()}
    dirs = [
        {
            t
            for p, t in table.items()
            if not p & (1 << i) and table.get(p | (1 << i)) == 1 - t
        }
        for i in range(feature_count)
    ]
    bits = [i for i, ds in enumerate(dirs) if len(ds) == 2 and not both & (1 << i)]
    outside = ((1 << feature_count) - 1) ^ sum(1 << j for j in bits)
    live = sum(2 if v == "both_live" else bool(dirs[i]) for i, v in enumerate(literals))
    return table, bits, outside, live, digest


def ordered_filter(care, outside):
    @lru_cache(None)
    def can(group, upstream, signed):
        if not group:
            return True
        contexts = {}
        for p, t in care.items():
            rest = p & ~group
            contexts.setdefault(rest & (outside | upstream), {}).setdefault(
                rest, []
            ).append((p & group, t))
        constraints = []
        for fibers in contexts.values():
            pairs = {
                (a, b)
                for fiber in fibers.values()
                for (a, t), (b, u) in combinations(fiber, 2)
                if t != u
            }
            if pairs:
                constraints.append(pairs)
        flip = group if signed else 0
        while True:
            if all(consistent(pairs, flip) for pairs in constraints):
                return True
            if not flip:
                return False
            flip = (flip - 1) & group

    def visit(groups, upstream=0):
        if not groups:
            return True
        for i, (g, signed) in enumerate(groups):
            if can(g, upstream, signed) and visit(
                groups[:i] + groups[i + 1 :], upstream | g
            ):
                return True
        return False

    return visit


def make_certificate(care, feature_count, model, budget, cases):
    table, bits, outside, _, digest = prepare(care, feature_count, model)
    return {
        "version": 1,
        "input_sha256": digest,
        "budget": budget,
        "cases": cases,
        "witnesses": orientation_witnesses(table, bits, outside),
    }


def verify_case(care, feature_count, model, certificate):
    table, bits, outside, live, digest = prepare(care, feature_count, model)
    require(
        set(certificate) == {"version", "input_sha256", "budget", "cases", "witnesses"},
        "certificate keys",
    )
    require(
        type(certificate["version"]) is int and certificate["version"] == 1,
        "certificate version",
    )
    require(certificate["input_sha256"] == digest, "care or source model mismatch")
    budget = certificate["budget"]
    require(type(budget) is int and budget >= 0, "invalid total budget")
    plans = certificate["cases"]
    require(isinstance(plans, list), "case list")
    for c in plans:
        require(set(c) == {"positive", "signed", "ordered", "partitions"}, "case keys")
        require(
            all(
                type(c[k]) is int and c[k] >= 0
                for k in ("positive", "signed", "partitions")
            ),
            "case counts",
        )
        require(type(c["ordered"]) is bool, "case mode")
    available = budget - model["fixed_cost"]
    for inversions in range(available + 1):
        binary = available - inversions
        if binary < max(0, live - 1) or (inversions == 0 and bits):
            continue
        groups = min(len(bits), binary - live + 1)
        exceptional = min(groups, max(0, inversions - 1))
        require(
            any(
                groups <= c["positive"] + c["signed"] and exceptional <= c["signed"]
                for c in plans
            ),
            f"uncovered topology at {binary} binary gates and {inversions} inversions",
        )
    general, positive = derive_edges(table, bits, outside, certificate["witnesses"])
    order = ordered_filter(table, outside)
    counts = []
    for c in plans:
        p, s = c["positive"], c["signed"]
        count = 0
        for groups in partitions(bits, positive, general, p, s):
            count += 1
            require(c["ordered"], "unordered compatible partition")
            require(
                not order(tuple((g, i >= p) for i, g in enumerate(groups))),
                "compatible branch ordering",
            )
        require(count == c["partitions"], "partition count mismatch")
        counts.append(count)
    return {
        "input_sha256": digest,
        "total_lower_bound": budget + 1,
        "essential_or_assumed_live_sources": live,
        "binate_slots": bits,
        "partition_counts": counts,
    }


def verify_optional_family(care, feature_count, model, certificates):
    """Prove a budget bound when either or both source polarities may be used.

    For each optional coordinate, positive-only and negative-only cases admit
    an unused source; a third case requires both physical leaves to be live.
    Missing, duplicate, extra, or differently budgeted cases are errors.
    """
    require(
        isinstance(model, dict) and set(model) == {"literals", "fixed_cost"},
        "family model keys",
    )
    literals = model["literals"]
    require(
        type(feature_count) is int
        and feature_count >= 0
        and isinstance(literals, (list, tuple))
        and len(literals) == feature_count,
        "family feature count",
    )
    require(
        all(t in ("positive", "negative", "optional") for t in literals),
        "family source polarity",
    )
    require(
        type(model["fixed_cost"]) is int and model["fixed_cost"] >= 0,
        "family fixed cost",
    )
    cases = {}
    budgets = set()
    optional = sum(t == "optional" for t in literals)
    require(
        isinstance(certificates, list) and len(certificates) == 3**optional,
        "incomplete optional-liveness family",
    )
    for record in certificates:
        require(
            isinstance(record, dict) and set(record) == {"literals", "certificate"},
            "family certificate keys",
        )
        labels = record["literals"]
        require(
            isinstance(labels, (list, tuple)) and len(labels) == feature_count,
            "family liveness arity",
        )
        for actual, declared in zip(labels, literals):
            require(
                (
                    actual in ("positive", "negative", "both_live")
                    if declared == "optional"
                    else actual == declared
                ),
                "case outside optional family",
            )
        key = tuple(labels)
        require(key not in cases, "duplicate optional-liveness case")
        certificate = record["certificate"]
        require(
            isinstance(certificate, dict) and type(certificate.get("budget")) is int,
            "family certificate budget",
        )
        budgets.add(certificate["budget"])
        cases[key] = certificate
    require(len(budgets) == 1, "family budgets differ")
    # Materialize iterables once so every liveness case receives identical rows.
    rows = list(care.items() if isinstance(care, dict) else care)
    results = []
    for key, certificate in cases.items():
        case_model = {"literals": list(key), "fixed_cost": model["fixed_cost"]}
        results.append(verify_case(rows, feature_count, case_model, certificate))
    return {
        "total_lower_bound": next(iter(budgets)) + 1,
        "case_count": len(results),
        "cases": results,
    }

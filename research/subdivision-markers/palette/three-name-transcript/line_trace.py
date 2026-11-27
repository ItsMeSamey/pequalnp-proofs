"""Replay a three-name line decision on the original binary input."""
from functools import partial
from exact_line import pivots, quotient


def prepare(columns, names, forced):
    names = tuple(names)
    pins = set(forced)
    if (len(names) != 3 or any(type(x) is not int or x < 0 for x in (*columns,*names))
            or len(pivots(names)) != 3 or any(type(i) is not int or i not in range(len(columns)) for i in pins)):
        raise ValueError("invalid physical input")
    table = pivots(columns[i] for i in pins)
    t,a,b = (quotient(x, table) for x in names)
    ids = [i for i in range(len(columns)) if i not in pins]
    q = [quotient(columns[i], table) for i in ids]
    if len(pivots((t,a,b))) < 3:
        tag = "pins_witness" if not t and len(pivots((a,b))) == 2 else "pins_conflict"
        return tag, (), ids
    if quotient(t, pivots(q)):
        return "outside", (), ids
    c = t ^ a ^ b
    return "search", [a,b,c,a^b,b^c,c^a] + q, ids


def valid_support(columns, names, forced, support):
    if not isinstance(support,(tuple,list)) or any(type(i) is not int or i not in range(len(columns)) for i in support):
        return False
    if len(set(support)) != len(support) or not set(forced) <= set(support):
        return False
    table = pivots(columns[i] for i in support)
    t,a,b = (quotient(x, table) for x in names)
    return t == 0 and len(pivots((a,b))) == 2


def replacement(columns, keep, basis):
    completion = list(basis)
    if len(basis) == 2:
        completion.append(basis[0] ^ basis[1])
    return [columns[i] for i in keep] + completion


def produce(columns, names, forced=(), *, executable="cmr-graphic"):
    from certified_graphic import graphic_or_obstruction, is_graphic_certified
    from exact_line import exact_line, interface
    from separations import find_separation
    from split_check import make_min_proof
    from terminal_graph import make_graph
    status, current, ids = prepare(columns, names, forced)
    if status == "pins_witness":
        return {"terminal":status, "support":sorted(set(forced)), "steps":[]}
    if status != "search":
        return {"terminal":status, "steps":[]}
    t = current[0] ^ current[1] ^ current[2]
    if t in current[6:]:
        return {"terminal":"single", "support":sorted(set(forced) | {ids[current[6:].index(t)]}), "steps":[]}
    steps = []
    initial = current
    while True:
        split = find_separation(current, range(6))
        if split is None:
            obstruction = graphic_or_obstruction(current, executable=executable)
            if obstruction is None:
                return {"terminal":"star", "steps":steps, "edges":make_graph(current, executable)}
            selected = exact_line(columns,*names,forced=forced,graphic=partial(is_graphic_certified,executable=executable))
            if selected is None:
                raise ValueError("terminal and original answers disagree")
            replay = initial
            for step in steps:
                step["minimum"] = make_min_proof(replay,len(step["interface"]))
                replay = replacement(replay,step["keep"],step["interface"])
            return {"terminal":"excluded","steps":steps,"obstruction":vars(obstruction),
                    "minimum":make_min_proof(current,3),"support":list(selected)}
        keep, drop = map(sorted,split)
        basis = interface([current[i] for i in keep], (current[i] for i in drop))
        steps.append({"keep":keep,"interface":basis})
        current = replacement(current,keep,basis)


def verify(columns, names, forced, cert):
    """Return the verified Boolean, raising on any invalid certificate."""
    from minor_check import verify_minor
    from split_check import check_min_proof
    from terminal_graph import check_star
    status, current, _ = prepare(columns,names,forced)
    kind, steps = cert["terminal"], cert["steps"]
    if not isinstance(steps,list):
        raise ValueError("invalid steps")
    if kind in ("pins_witness","single"):
        if steps or (kind == "pins_witness" and status != kind) or not valid_support(columns,names,forced,cert["support"]):
            raise ValueError("invalid original support")
        return True
    if kind in ("pins_conflict","outside"):
        if steps or kind != status:
            raise ValueError("invalid initial rejection")
        return False
    if status != "search":
        raise ValueError("unreachable search branch")
    for step in steps:
        keep, basis = step["keep"], step["interface"]
        if (not isinstance(keep,list) or any(type(i) is not int or i not in range(len(current)) for i in keep)
                or sorted(set(keep)) != keep or keep[:6] != list(range(6))
                or not isinstance(basis,list) or len(basis)>2 or any(type(x) is not int or x<0 for x in basis)):
            raise ValueError("invalid split encoding")
        kept = set(keep)
        left = pivots(current[i] for i in keep)
        right = pivots(v for i,v in enumerate(current) if i not in kept)
        k = len(basis)
        if (min(len(left),len(right)) <= k or len(left)+len(right)-len(pivots(current)) != k
                or len(pivots(basis)) != k or any(quotient(x,left) or quotient(x,right) for x in basis)
                or (kind == "excluded" and not check_min_proof(current,k,step.get("minimum")))
                or (kind == "star" and "minimum" in step)):
            raise ValueError("invalid vertical separation or interface")
        current = replacement(current,keep,basis)
    if kind == "star" and check_star(current,cert["edges"]):
        return False
    if kind == "excluded":
        o = cert["obstruction"]
        if (verify_minor(current,o["retain"],o["contract"],o["delete"],o["target"])
                and check_min_proof(current,3,cert["minimum"])
                and valid_support(columns,names,forced,cert["support"])):
            return True
    raise ValueError("invalid terminal certificate")

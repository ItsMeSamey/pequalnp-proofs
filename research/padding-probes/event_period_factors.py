"""Branch over maximal translation-period cosets of each explicit factor."""
from itertools import product
from event_affine_factors import solve as gaussian


def period_partition(points):
    points = frozenset(points)
    if not points:
        return ()
    origin = min(points)
    periods = [x ^ origin for x in points
               if all((y ^ x ^ origin) in points for y in points)]
    remaining = set(points)
    parts = []
    while remaining:
        base = min(remaining)
        coset = frozenset(base ^ h for h in periods)
        remaining.difference_update(coset)
        parts.append(coset)
    return tuple(parts)


def solve(domains, constraints, output, *, codebooks=None, choice_cap=None):
    """choice_cap counts complete coset tuples passed to Gaussian solving."""
    if choice_cap is not None and (type(choice_cap) is not int or choice_cap < 0):
        raise ValueError("invalid choice cap")
    domains = {v: tuple(records) for v, records in domains.items()}
    if output not in domains or any(type(x) not in (int, bool) or x not in (0, 1)
                                     for x in domains[output]):
        raise ValueError("invalid output domain")
    custom = {} if codebooks is None else dict(codebooks)
    if custom.keys() - domains.keys():
        raise ValueError("codebook on unknown variable")
    books = {}
    widths = {}
    for v, records in domains.items():
        book = dict(custom[v]) if v in custom else {x:i for i,x in enumerate(records)}
        if (len(set(records)) != len(records) or not set(records) <= book.keys()
                or any(type(x) is not int or x < 0 for x in book.values())
                or len(set(book.values())) != len(book)):
            raise ValueError("invalid codebook or domain")
        books[v] = book
        widths[v] = max((x.bit_length() for x in book.values()), default=0)
    factors = []

    def add(scope, decoding):
        parts = period_partition(decoding)
        factors.append((scope, [frozenset(decoding[x] for x in part) for part in parts]))

    for v, records in domains.items():
        add((v,), {books[v][x]: x for x in records})
    live = {v:set(records) for v,records in domains.items()}
    for u,v,pairs in constraints:
        pairs = [(x,y) for x,y in pairs if x in live[u] and y in live[v]]
        if u == v:
            add((u,), {books[u][x]:x for x,y in pairs if x == y})
        else:
            add((u,v), {books[u][x] | (books[v][y] << widths[u]):(x,y) for x,y in pairs})

    sizes = tuple(len(parts) for _,parts in factors)
    count = 1
    for size in sizes:
        count *= size
    metrics = dict(coset_counts=sizes, choice_product=count, choices=0)
    witnesses = {}
    def result(status):
        out = dict(status=status, metrics=metrics, witnesses=witnesses)
        if status == "constant":
            out["value"] = next(iter(witnesses))
        if status == "unknown":
            out["reason"] = "choice cap"
        return out

    for choices in product(*(parts for _,parts in factors)):
        if choice_cap is not None and metrics["choices"] >= choice_cap:
            return result("unknown")
        metrics["choices"] += 1
        narrowed = {v:set(records) for v,records in domains.items()}
        relations = []
        for (scope,_), allowed in zip(factors,choices):
            if len(scope) == 1:
                narrowed[scope[0]].intersection_update(allowed)
            else:
                relations.append((*scope,allowed))
        solved = gaussian(narrowed, relations, output, codebooks=books)
        if solved["status"] == "unknown":
            raise ArithmeticError("coset intersection lost affinity")
        witnesses.update(solved["witnesses"])
        if len(witnesses) == 2:
            return result("pair")
    return result("constant" if witnesses else "empty")

"""Nonterminal-layer census for minimal three-connected two-pin odd supports.

T[v][u] counts prefix selections for incoming parity v and selected boundary
mask u, with multiplicities saturated at two.
"""

from collections import Counter
from itertools import product, combinations
from pathlib import Path
import json
import argparse


def parity(v):
    return v.bit_count() % 2


def root(R):
    rows = R["rows"]
    n = len(rows)
    J = R["ports"]

    def proj(z):
        return sum(((z >> i) & 1) << j for j, i in enumerate(J))

    live = sum(1 << i for i in J)
    T = [{} for _ in range(1 << len(J))]
    for s in range(3, 1 << n, 4):
        error = sum((1 ^ parity(s & r)) << i for i, r in enumerate(rows) if s >> i & 1)
        if error & ~live:
            continue
        u, e = proj(s), proj(error)
        for v in range(len(T)):
            if v & u == e:
                T[v][u] = min(2, 1 + T[v].get(u, 0))
    return [rows[j].bit_count() for j in J], T


def grow(deg, T):
    k = len(deg)
    full = (1 << k) - 1
    opts = [[f - d for f in (3, 5) if f >= d] for d in deg]
    types = [t for t in range(1, 1 << k) if not any(parity(t & u) for u in T[t])]
    pairs = {}
    for t, h in product(types, repeat=2):
        forbidden = {
            1 ^ parity(t & u) for u in T[t ^ h] if parity(t & u) == parity(h & u)
        }
        pairs[t, h] = set((0, 1)) - forbidden

    def visit(d, ts, start):
        if any(d):
            for j in range(start, len(types)):
                t = types[j]
                e = [n - ((t >> i) & 1) for i, n in enumerate(d)]
                if min(e) >= 0 and all(pairs[t, h] for h in ts):
                    yield from visit(e, ts + [t], j)
            return
        if len(ts) < 3:
            return
        l = len(ts)

        sig = [0] * (1 << l)
        for s in range(1, 1 << l):
            lo = s & -s
            sig[s] = sig[s ^ lo] ^ ts[lo.bit_length() - 1]
        old = T[sig[-1]]
        if old.get(full) != 1 or any(
            u != full and not any(parity((full ^ u) & t) for t in ts) for u in old
        ):
            return
        ext = [0] * l
        optional = []
        for i, j in combinations(range(l), 2):
            p = pairs[ts[i], ts[j]]
            if len(p) == 2:
                optional.append((i, j))
            elif 1 in p:
                ext[i] |= 1 << j
                ext[j] |= 1 << i
        yield from edge_sweep(l, ts, sig, ext, optional, T)

    for ds in product(*opts):
        if sum(d > 0 for d in ds) >= 3:
            yield from visit(ds, [], 0)


def edge_sweep(l, ts, sig, ext, optional, T, idx=0):
    ds = [ext[i].bit_count() + t.bit_count() for i, t in enumerate(ts)]
    if max(ds) > 5 or sum(d < 5 for d in ds) < 3:
        return
    if idx < len(optional):
        i, j = optional[idx]
        yield from edge_sweep(l, ts, sig, ext, optional, T, idx + 1)
        ext[i] ^= 1 << j
        ext[j] ^= 1 << i
        yield from edge_sweep(l, ts, sig, ext, optional, T, idx + 1)
        ext[i] ^= 1 << j
        ext[j] ^= 1 << i
        return
    J = [j for j, d in enumerate(ds) if d < 5]
    keep = sum(1 << j for j in J)

    def packed(x):
        return sum(((x >> j) & 1) << i for i, j in enumerate(J))

    P = [{} for _ in range(1 << len(J))]
    for s, t in enumerate(sig):
        p = packed(s)
        for u, c in T[t].items():
            err = s & sum(
                (1 ^ parity(u & ts[j]) ^ parity(s & ext[j])) << j for j in range(l)
            )
            if err == 0:
                return
            if err & ~keep:
                continue
            e = packed(err)
            for v in range(len(P)):
                if p & v == e:
                    P[v][p] = min(2, c + P[v].get(p, 0))
    dd = [ds[j] for j in J]
    mask = sum((1 ^ (d & 1)) << j for j, d in enumerate(dd))
    if P[mask].get((1 << len(J)) - 1) != 1:
        return
    yield dd, P, tuple(ts), tuple(ext)


def key(D, T):
    return tuple(D), tuple(tuple(sorted(a.items())) for a in T)


def glue(rows, ports, incidence, internal):
    n = len(rows)
    next_rows = list(rows) + [a << n for a in internal]
    for i, neighbors in enumerate(incidence):
        for j, old in enumerate(ports):
            if (neighbors >> j) & 1:
                next_rows[n + i] |= 1 << old
                next_rows[old] |= 1 << (n + i)
    next_ports = [i for i in range(n, len(next_rows)) if next_rows[i].bit_count() < 5]
    return next_rows, next_ports


def initial_histories():
    source = Path(__file__).with_name("degree_five_common_core_census.json")
    for group in json.loads(source.read_text()):
        for record in group["orbits"]:
            if record["all_pieces_reach_port"]:
                ports = [
                    i
                    for i, options in enumerate(record["exterior_degrees"], 2)
                    if max(options) > 0
                ]
                rows = record["rows"]
                degrees, table = root(dict(rows=rows, ports=ports))
                yield degrees, table, rows, ports


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check-raw",
        action="store_true",
        help="recompute child tables from original graph selections",
    )
    check = parser.parse_args().check_raw
    current = list(initial_histories())
    totals = []
    while current:
        distinct = len({key(d, t) for d, t, _, _ in current})
        cap = max(
            len(rows) + sum(5 - d for d in degrees) for degrees, _, rows, _ in current
        )
        totals.append((len(current), distinct, cap))
        print(
            "depth",
            len(totals) - 1,
            "histories",
            len(current),
            "states",
            distinct,
            "order with one final layer at most",
            cap,
            flush=True,
        )
        next_histories = []
        for degrees, table, rows, ports in current:
            for d, t, incidence, internal in grow(degrees, table):
                graph, new_ports = glue(rows, ports, incidence, internal)
                if check:
                    assert root(dict(rows=graph, ports=new_ports)) == (d, t)
                next_histories.append((d, t, graph, new_ports))
        current = next_histories
    assert [s for h, s, b in totals] == [52, 66, 47, 14]
    assert max(b for h, s, b in totals) == 30


if __name__ == "__main__":
    main()

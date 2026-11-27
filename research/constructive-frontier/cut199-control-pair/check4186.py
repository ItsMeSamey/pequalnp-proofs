"""Check non-minimality-independent conditions of Lean L_meta_4186.

Input JSON: {"n":3,"edges":[[0,1],[0,2]],"gates":[["or",1,2],["and",0,3]],"output":4}.
Gate indices in diagnostics are zero based. Output is a wire. AO2 violations
are rejected as invalid inputs. Computational cost is exponential in n.
"""
import argparse
import json
from itertools import combinations
from pathlib import Path


def natural(v):
    return type(v) is int and v >= 0


def check(n, edges, gates, output):
    if not natural(n) or not natural(output):
        raise ValueError("expected natural n and output")
    pairs = set()
    neighbors = [set() for _ in range(n)]
    for u, v in edges:
        if not (natural(u) and natural(v) and u < n and v < n and u != v):
            raise ValueError("invalid simple graph edge")
        pairs.add(tuple(sorted((u, v))))
        neighbors[u].add(v)
        neighbors[v].add(u)
    no_four_cycle = all(len(a & b) <= 1 for a, b in combinations(neighbors, 2))
    assignments = range(1 << n)
    bits = [sum(1 << x for x in assignments if x >> u & 1) for u in range(n)]
    target = 0
    for u, v in pairs:
        target |= bits[u] & bits[v]
    cones = [set() for _ in range(n)]  # gate indices inside wire cone, including its root
    or_reach = [set() for _ in range(n)]
    or_in = [{u} for u in range(n)]
    below, tops, junk, or_n, or_t = set(), set(), set(), set(), set()
    strict = []
    operands = []
    for i, gate in enumerate(gates):
        if isinstance(gate, dict):
            op, args = gate["op"], gate["inputs"]
        else:
            op, *args = gate
        if op not in ("and", "or") or len(args) != 2 or not all(natural(w) and w < n+i for w in args):
            raise ValueError(f"gate {i} violates IsAO2")
        a, b = args
        operands.append((a, b))
        strict.append(cones[a] | cones[b])
        cones.append(strict[-1] | {i})
        if op == "and":
            bits.append(bits[a] & bits[b])
            or_in.append(set())
            or_reach.append({i})
        else:
            bits.append(bits[a] | bits[b])
            or_in.append(or_in[a] | or_in[b])
            or_reach.append(or_reach[a] | or_reach[b] | {i})
        if not bits[-1] & ~target:
            below.add(i)
            (tops if op == "and" else or_t).add(i)
        else:
            (junk if op == "and" else or_n).add(i)

    centreless, star_edges, eligible = set(), set(), set()
    for i in tops:
        a, b = operands[i]
        if not or_in[a] or not or_in[b]:
            centreless.add(i)
        star_edges.update(tuple(sorted((u, v))) for u in or_in[a] for v in or_in[b])
        for leaf, other in ((a, b), (b, a)):
            if len(or_in[other]) == 1:
                eligible.update(or_reach[leaf])
    lam = {i for i in or_n & eligible if all(or_in[w] for w in operands[i])}
    ustar = pairs - star_edges
    def is_cover(x):
        return all((x >> u | x >> v) & 1 for u, v in pairs)
    cover = min((x for x in assignments if is_cover(x)), key=int.bit_count)
    lhs = cover.bit_count() + len(ustar)
    rhs = len(tops - centreless) + 2*len(centreless) + len(junk) + len(or_n - lam)
    top_form = all(not (tops & strict[i]) for i in tops | junk)
    computes = (bits[output] if output < len(bits) else 0) == target
    return dict(isAO2=True, noFourCycle=no_four_cycle, edgeNonempty=bool(pairs),
                computes=computes, topForm=top_form, belowF=sorted(below),
                inCone=[sorted(s) for s in strict], orIn=[sorted(s) for s in or_in],
                lam=sorted(lam), centreless=sorted(centreless), junk=sorted(junk),
                tops=sorted(tops), orN=sorted(or_n), orT=sorted(or_t),
                starEdges=sorted(star_edges), Ustar=sorted(ustar),
                minimumCover=[i for i in range(n) if cover >> i & 1],
                tau=cover.bit_count(), lhs=lhs, rhs=rhs, leastSizeVerified=None,
                candidatePendingMinimality=bool(pairs) and no_four_cycle and computes and top_form and lhs > rhs)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidate", type=Path)
    data = json.loads(parser.parse_args().candidate.read_text())
    print(json.dumps(check(data["n"], data["edges"], data["gates"], data["output"])))

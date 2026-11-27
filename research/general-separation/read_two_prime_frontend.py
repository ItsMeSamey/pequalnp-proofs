"""Signed CNF to a positive width-three, exactly-read-twice CNF and MLE point.

Source literal ±j refers to declared variable 1<=j<=n. Unused variables count.
compile_cnf returns the actual positive clauses (one-based IDs) and success
weights indexed by ID minus one. The evaluation equals the source model count
modulo the specified fixed prime >=5. With selectors {j:X}, each model instead
contributes the product of X over its true selected variables. An omitted
selector creates no gadget. prime=None uses exact rational arithmetic; in
particular the unweighted evaluation is the ordinary integer model count.
Rational weights are signed interpolation parameters. For a fixed prime or
in rational mode, construction takes polynomial bit time in n, the source
encoding and the bit lengths of the supplied numeric parameters.
This frontend emits an instance, not a generic efficient evaluator for it.
"""
import argparse
from fractions import Fraction
import json
from math import isqrt


def _field(prime):
    if prime is None:
        return Fraction, lambda a, b: a / b
    if (type(prime) is not int or prime < 5 or
            any(prime % j == 0 for j in range(2, isqrt(prime) + 1))):
        raise ValueError("expected a fixed prime >=5, or None for the rationals")

    def residue(value):
        value = Fraction(value)
        return value.numerator * pow(value.denominator, -1, prime) % prime

    return residue, lambda a, b: a * pow(b, -1, prime) % prime


def compile_cnf(n, clauses, prime, *, selectors=None, t=2):
    if type(n) is not int or n < 0:
        raise ValueError("invalid number of declared variables")
    field, divide = _field(prime)
    one, t = field(1), field(t)
    if t in (field(0), one, field(-1)):
        raise ValueError("interaction parameter must differ from zero and ±one")
    selectors = {} if selectors is None else dict(selectors)
    if any(type(j) is not int or not 1 <= j <= n for j in selectors):
        raise ValueError("invalid selector index")

    # Hard-core vertices carry (constant activity, optional selector index).
    vertices, edges = [], []
    def vertex(activity, selector=None):
        vertices.append((field(activity), selector))
        return len(vertices)-1

    literals = {}
    for j in range(1, n+1):
        pos, neg, mediator = vertex(1), vertex(1), vertex(-1)
        literals[j], literals[-j] = pos, neg
        edges.extend(((pos, neg), (pos, mediator), (neg, mediator)))
    for clause in clauses:
        med = vertex(-1)
        seen = set()
        for literal in clause:
            if type(literal) is not int or literal not in literals:
                raise ValueError("invalid signed literal")
            if literal not in seen:
                edges.append((med, literals[literal]))
                seen.add(literal)
    for j in sorted(selectors):
        edges.append((vertex(-1, j), literals[-j]))

    # Each original edge gets named incidence copies at its two endpoints.
    incidences = [[] for _ in vertices]
    for a, b in edges:
        incidences[a].append(len(incidences[a]))
        incidences[b].append(len(incidences[b]))
    expanded, terminals, paths, internals = [], [], [], []
    expanded_count = 0
    for slots in incidences:
        chain = list(range(expanded_count, expanded_count+len(slots)+2))
        expanded_count += len(chain)
        terminals.append((chain[0], chain[-1]))
        paths.append(chain)
        slots[:] = chain[1:-1]
        for a, b in zip(chain, chain[1:]):
            current = a
            for activity in (-1, -1, 1, -1, -1):
                new = expanded_count
                expanded_count += 1
                internals.append((new, field(activity)))
                expanded.append((current, new))
                current = new
            expanded.append((current, b))
    used = [0]*len(vertices)
    for a, b in edges:
        expanded.append((incidences[a][used[a]], incidences[b][used[b]]))
        used[a] += 1
        used[b] += 1

    weights, physical = [], [[] for _ in range(expanded_count)]
    def variable(weight):
        weights.append(field(weight))
        return len(weights)

    for a, b in expanded:
        left, right = variable(one-t), variable(one-t)
        physical[a].append(left)
        physical[b].append(right)
        physical.append([left, right])
    q = divide(t, field(one+t))
    base = [field(-(q**len(row))) for row in physical[:expanded_count]]
    privates, selector_vars = [], {}
    def private(site, failure):
        raw = variable(one-failure)
        physical[site].append(raw)
        privates.append(raw)
        return raw

    for site, activity in internals:
        private(site, divide(activity, base[site]))
    for (activity, j), chain, (first, last) in zip(vertices, paths, terminals):
        baseline = one
        for site in chain:
            baseline = field(baseline * base[site])
        private(first, divide(activity, baseline))
        if j is None:
            private(last, one)
        else:
            selector_vars[j] = private(last, one-field(selectors[j]))

    factor = field(one-t*t)
    exponent = len(expanded)
    scalar = factor**exponent if prime is None else pow(factor, exponent, prime)
    normalization = variable(divide(one, scalar))
    physical.extend(([normalization], [normalization]))
    for raw in privates:
        guard = variable(one)
        physical.extend(([raw, guard], [guard]))
    return dict(prime=prime, t=t, clauses=tuple(map(tuple, physical)),
                weights=tuple(weights), expanded_edges=exponent,
                normalization_variable=normalization, selector_variables=selector_vars)


def main():
    import sys
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prime", type=int, help="omit for exact rational weights")
    parser.add_argument("--t", type=int, default=2)
    args = parser.parse_args()
    data = json.load(sys.stdin)
    selectors = {int(j): x for j, x in data.get("selectors", {}).items()}
    result = compile_cnf(data["n"], data["clauses"], args.prime,
                         selectors=selectors, t=args.t)
    print(json.dumps(result, default=str, separators=(",", ":")))


if __name__ == "__main__":
    main()

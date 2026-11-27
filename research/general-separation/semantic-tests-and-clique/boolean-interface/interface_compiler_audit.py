"""Cross-check compiler outputs against truth tables and formal polynomial coefficients."""
import argparse
import json
import random
from pathlib import Path


def truth(spec, mask):
    names = spec["inputs"]
    assignment = {name: mask >> i & 1 for i, name in enumerate(names)}
    values = []
    for tag, *args in spec["gates"]:
        if tag == "var":
            value = assignment[args[0]]
        elif tag == "const":
            value = args[0]
        elif tag == "gate":
            table, left, right = args
            value = (table >> (2 * values[left] + values[right])) & 1
        else:
            raise ValueError(f"unknown source gate {tag!r}")
        values.append(value)
    return values[spec["output"]]


def mobius_coefficients(table, n, p):
    coefficients = list(table)
    for bit in range(n):
        for subset in range(len(table)):
            if subset >> bit & 1:
                coefficients[subset] = (coefficients[subset] - coefficients[subset ^ (1 << bit)]) % p
    return {
        tuple((subset >> i) & 1 for i in range(n)): value
        for subset, value in enumerate(coefficients) if value
    }


def output_dependencies(nodes, output):
    if not isinstance(output, int) or not 0 <= output < len(nodes):
        raise ValueError("invalid output reference")
    needed = {output}
    for i in range(output, -1, -1):
        if i not in needed:
            continue
        tag, *args = nodes[i]
        if tag in ("add", "mul"):
            if len(args) != 2 or any(not isinstance(j, int) or not 0 <= j < i for j in args):
                raise ValueError(f"invalid operands at node {i}")
            needed.update(args)
        elif tag not in ("const", "var") or len(args) != 1:
            raise ValueError(f"invalid arithmetic node {i}")
    return sorted(needed)


def audit(spec, p, optimized, compiler=None):
    if compiler is None:
        from interface_compiler import compile_dag as compiler
    result = compiler(spec, p, optimized=optimized)
    nodes, output = result["nodes"], result["output"]
    needed = output_dependencies(nodes, output)
    names = spec["inputs"]
    n = len(names)
    if n > 12:
        raise ValueError("exhaustive audit limited to twelve input variables")
    table = [truth(spec, address) for address in range(1 << n)]
    expected = mobius_coefficients(table, n, p)
    indices = {name: i for i, name in enumerate(names)}
    zero = (0,) * n
    polynomials = {}
    for i in needed:
        tag, *args = nodes[i]
        if tag == "const":
            c = args[0] % p
            current = {zero: c} if c else {}
        elif tag == "var":
            j = indices[args[0]]
            current = {tuple(int(k == j) for k in range(n)): 1}
        else:
            a, b = (polynomials[j] for j in args)
            if tag == "add":
                current = dict(a)
                for term, value in b.items():
                    current[term] = (current.get(term, 0) + value) % p
            else:
                if len(a) * len(b) > 500_000:
                    raise ValueError("intermediate multiplication exceeds audit cap")
                current = {}
                for left, u in a.items():
                    for right, v in b.items():
                        # Ordinary polynomial ring: repeated variables retain their powers.
                        term = tuple(x + y for x, y in zip(left, right))
                        current[term] = (current.get(term, 0) + u * v) % p
            current = {term: c for term, c in current.items() if c}
        polynomials[i] = current

    for address, bit in enumerate(table):
        values = {}
        for i in needed:
            tag, *args = nodes[i]
            if tag == "const":
                v = args[0]
            elif tag == "var":
                v = address >> indices[args[0]] & 1
            elif tag == "add":
                v = values[args[0]] + values[args[1]]
            else:
                v = values[args[0]] * values[args[1]]
            values[i] = v % p
        if values[output] != bit:
            raise AssertionError(f"Boolean evaluation differs at address {address}, field {p}")
    actual = polynomials[output]
    if actual != expected:
        term = next(t for t in sorted(actual.keys() | expected.keys()) if actual.get(t) != expected.get(t))
        raise AssertionError(f"formal coefficient {term}: got {actual.get(term, 0)}, expected {expected.get(term, 0)}, field {p}")
    return len(table)


def cases(seed):
    rng = random.Random(seed)
    for gate in range(16):
        yield {"inputs": ["x", "y"], "gates": [["var", "x"], ["var", "y"], ["gate", gate, 0, 1]], "output": 2}
    for n in (1, 2, 3, 4):
        names = [f"x{i}" for i in range(n)]
        for _ in range(10):
            gates = [["var", v] for v in names] + [["const", 0], ["const", 1]]
            for _ in range(8):
                left = rng.randrange(len(gates))
                right = rng.choice([left, rng.randrange(len(gates))])
                gates.append(["gate", rng.randrange(16), left, right])
            yield {"inputs": names, "gates": gates, "output": len(gates) - 1}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixtures", type=Path, nargs="*")
    parser.add_argument("--seed", type=int, default=10513)
    args = parser.parse_args()
    specs = list(cases(args.seed))
    for path in args.fixtures:
        data = json.loads(path.read_text())
        specs.extend(data if isinstance(data, list) else [data])
    count = 0
    evaluations = 0
    for case_index, spec in enumerate(specs):
        for p in (2, 5):
            for optimized in (False, True):
                try:
                    evaluations += audit(spec, p, optimized)
                except Exception as error:
                    raise RuntimeError(f"case {case_index}, p={p}, optimized={optimized}") from error
                count += 1
    print(f"{count} formal comparisons and {evaluations} Boolean evaluations passed across {len(specs)} DAGs")


if __name__ == "__main__":
    main()

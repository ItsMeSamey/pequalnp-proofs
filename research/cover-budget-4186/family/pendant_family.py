"""Build the triangle with b leaves at c and d leaves at a, with its AO2 circuit."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path


def build(b, d):
    if any(type(k) is not int or k < 1 for k in (b, d)):
        raise ValueError("b and d must be positive integers")
    n = 3 + b + d
    bs, ds = range(3, 3 + b), range(3 + b, n)
    edges = [(0, 1), (0, 2), (1, 2)] + [(1, u) for u in bs] + [(0, v) for v in ds]
    gates = []

    def gate(op, left, right):
        gates.append([op, left, right])
        return n + len(gates) - 1

    def fold(root, leaves):
        for leaf in leaves:
            root = gate("or", root, leaf)
        return root

    ab, cd = fold(0, bs), fold(1, ds)
    dirty = gate("and", ab, cd)
    mixed = gate("or", dirty, 2)
    centres = gate("or", 0, 1)
    output = gate("and", mixed, centres)
    return dict(n=n, edges=edges, gates=gates, output=output)


def lean(b, d):
    p = build(b, d)
    edges = ", ".join(f"({u}, {v})" for u, v in p["edges"])
    gates = ", ".join(f"⟨.{op}, [{u}, {v}]⟩" for op, u, v in p["gates"])
    return (f"import PEqualNP.Defs\n\nnamespace Pendant{b}x{d}\n"
            f"abbrev G := PEqualNP.EdgeOwnership.edgeGraph {p['n']} [{edges}]\n"
            f"def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[{gates}], {p['output']}⟩\n"
            f"end Pendant{b}x{d}")


def check_small(path=None):
    if path is None:
        local = Path(__file__).resolve().parent.parent / "enumeration" / "check4186.py"
        path = local if local.is_file() else Path(__file__).resolve().parents[2] / "site-team-05" / "check4186.py"
    expected = "a89867d05dc2afb95df980463d98b76e7989c2f7b97dbcaa15ecf902b852b61f"
    if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        raise ValueError("checker digest differs from the audited enumeration manifest")
    spec = importlib.util.spec_from_file_location("check4186", path)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    for b in range(1, 4):
        for d in range(1, 4):
            data = build(b, d)
            result = checker.check(**data)
            k = b + d
            expected = dict(isAO2=True, computes=True, noFourCycle=True, edgeNonempty=True,
                            topForm=True, belowF=[k + 3], tops=[k + 3], junk=[k],
                            centreless=[], orT=[], lam=[k + 2],
                            orN=[*range(k), k + 1, k + 2], tau=2, lhs=k + 3, rhs=k + 3,
                            starEdges=[(0, 2), (1, 2)],
                            Ustar=sorted(set(data["edges"]) - {(0, 2), (1, 2)}))
            assert len(data["gates"]) == k + 4
            for field, value in expected.items():
                if result[field] != value:
                    raise AssertionError((b, d, field, value, result[field]))
    return "Verified all nine pairs with 1 ≤ b,d ≤ 3 against check4186.py."


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("b", type=int, nargs="?")
    parser.add_argument("d", type=int, nargs="?")
    parser.add_argument("--format", choices=("json", "lean"), default="json")
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--checker", type=Path, help="pinned finite checker for --test")
    args = parser.parse_args()
    if args.test:
        print(check_small(args.checker))
    elif args.b is None or args.d is None:
        parser.error("supply both b and d")
    else:
        print(lean(args.b, args.d) if args.format == "lean" else json.dumps(build(args.b, args.d)))

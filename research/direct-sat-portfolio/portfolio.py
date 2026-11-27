"""Deterministic scalar SAT on indexed affine-input AND circuits."""
import argparse
import importlib
import json
import time
import sys

from cofactor import compact, rewrite

ROUTES = ("affine_quotient", "backward_bank", "reachable_span", "grouped_mask")


def natural(name, value):
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer")


def validate(n, gates, output):
    natural("n", n)
    natural("output", output)
    result = []
    for index, pair in enumerate(gates):
        if len(pair) != 2:
            raise ValueError("each AND needs two operands")
        for mask in pair:
            natural("operand", mask)
            if mask.bit_length() > n + 1 + index:
                raise ValueError(f"forward reference in AND {index}")
        result.append(tuple(pair))
    if output.bit_length() > n + 1 + len(result):
        raise ValueError("missing output signal")
    return tuple(result)


def evaluate(n, gates, output, x):
    """Direct evaluation of an already validated presentation."""
    signals = (x << 1) | 1
    for index, (left, right) in enumerate(gates):
        if (signals & left).bit_count() % 2 and (signals & right).bit_count() % 2:
            signals |= 1 << (n + index + 1)
    return (signals & output).bit_count() % 2


def simplify(n, gates, output, limit):
    if output.bit_length() <= n + 1:
        return (), output, 0, []
    gates, output = compact(n, gates, output)
    tested = 0
    accepted = []
    while tested < limit:
        improved = False
        for index in reversed(range(len(gates))):
            for side, form in enumerate(gates[index]):
                bits = form & ~1
                while bits and tested < limit:
                    bit = bits & -bits
                    bits ^= bit
                    pivot = bit.bit_length() - 1
                    candidate, last = rewrite(n, gates, output, index, side, pivot)
                    tested += 1
                    if len(candidate) < len(gates):
                        accepted.append([index, side, pivot, len(gates), len(candidate)])
                        gates, output = candidate, last
                        improved = True
                        break
                if improved or tested == limit:
                    break
            if improved or tested == limit:
                break
        if not improved:
            break
    return tuple(gates), output, tested, accepted


def solve(n, gates, output, *, budget=4096, rewrite_budget=8, routes=None):
    started = time.perf_counter_ns()
    original = validate(n, gates, output)
    natural("budget", budget)
    natural("rewrite_budget", rewrite_budget)
    names = tuple(ROUTES if routes is None else routes)
    if len(set(names)) != len(names) or any(name not in ROUTES for name in names):
        raise ValueError("unrecognized or duplicate route")
    reduced, last, tested, changes = simplify(n, original, output, rewrite_budget)
    validate(n, reduced, last)
    encoded = json.dumps([hex(n), [[hex(a), hex(b)] for a, b in original], hex(output)], separators=(",", ":"))
    cost = dict(budget=budget, rewrite_budget=rewrite_budget, raw_n=n, raw_ands=len(original), retained_ands=len(reduced),
                canonical_json_bytes=len(encoded.encode()), rewrite_trials=tested,
                accepted_rewrites=changes, attempts=[], requested_routes=names,
                fallback_evaluations=0, replay_evaluations=0)

    def finish(route, witness):
        if witness is not None:
            if type(witness) is not int or not 0 <= witness < 1 << n:
                raise RuntimeError(f"{route} supplied an invalid input")
            cost["replay_evaluations"] += 1
            if not evaluate(n, original, output, witness):
                raise RuntimeError(f"{route} witness failed original evaluation")
        cost["elapsed_ns"] = time.perf_counter_ns() - started
        return dict(status="sat" if witness is not None else "unsat",
                    witness=witness, route=route, verified=witness is not None, cost=cost)

    if last.bit_length() <= n + 1:
        variable_mask = last >> 1
        witness = 0 if last & 1 else (variable_mask & -variable_mask or None)
        return finish("affine_output", witness)

    candidates = []
    for name in names:
        backend = importlib.import_module(name)
        tick = time.perf_counter_ns()
        try:
            estimate = backend.estimate(n, reduced, last)
        except TimeoutError:
            cost["attempts"].append(dict(route=name, status="estimate_timeout",
                                         estimate_ns=time.perf_counter_ns()-tick))
            continue
        record = dict(route=name, estimate=estimate, estimate_ns=time.perf_counter_ns()-tick)
        cost["attempts"].append(record)
        if estimate is not None:
            natural("estimate", estimate)
        if estimate is None or estimate > budget or not budget:
            record["status"] = "budget_or_ineligible"
        else:
            record["status"] = "eligible"
            candidates.append((estimate, name, backend, record))
    for _, name, backend, record in sorted(candidates):
        tick = time.perf_counter_ns()
        try:
            result = backend.solve(n, reduced, last, budget=budget)
        except TimeoutError:
            record.update(status="timeout", solve_ns=time.perf_counter_ns()-tick)
            continue
        record.update(status=result["status"], cost=result.get("cost", {}),
                      solve_ns=time.perf_counter_ns()-tick)
        if result["status"] == "sat":
            if result.get("witness") is None:
                raise RuntimeError(f"{name} omitted its witness")
            return finish(name, result["witness"])
        if result["status"] == "unsat":
            return finish(name, None)
        if result["status"] not in ("skip", "unknown", "timeout"):
            raise RuntimeError(f"{name} returned an unknown status")
    for x in range(1 << n):
        cost["fallback_evaluations"] += 1
        if evaluate(n, original, output, x):
            return finish("exhaustive", x)
    return finish("exhaustive", None)


if __name__ == "__main__":
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)  # CLI accepts arbitrary-length decimal JSON masks.
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("circuit", help="JSON object with n, gates and output")
    parser.add_argument("--budget", type=int, default=4096)
    parser.add_argument("--rewrite-budget", type=int, default=8)
    parser.add_argument("--routes", nargs="*", choices=ROUTES)
    args = parser.parse_args()
    with open(args.circuit, encoding="utf8") as inp:
        data = json.load(inp)
    print(json.dumps(solve(**data, budget=args.budget, rewrite_budget=args.rewrite_budget,
                           routes=args.routes), sort_keys=True))

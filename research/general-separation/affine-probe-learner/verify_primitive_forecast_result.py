"""Verify a decoded JSON extractor certificate against independent public inputs.

CLI: python verify_primitive_forecast_result.py --learner module:callable
stdin: {"expected":{"n":...,"F":...,"S":...,"bound":...},"result":...}
Cost fields are diagnostic only. UNSAT uses the caller's mistake-bound premise.
"""
import argparse
import importlib
import json
import sys

from check_primitive_rewrite_chain import verify as verify_chain
from primitive_rewrite_chain import Chain, Step, endpoint, evaluate, normalize


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def natural(x):
    require(type(x) is int and x >= 0, "expected nonnegative integer")
    return x


def sequence(x):
    require(type(x) in (list, tuple), "expected sequence")
    return x


def bit(x):
    require(type(x) is int and x in (0, 1), "expected integer bit")
    return x


def circuit(n, encoded):
    gates, out = sequence(encoded)
    result = []
    for i, pair in enumerate(sequence(gates)):
        a, b = sequence(pair)
        require(all(type(w) is int and -2 <= w < n+i for w in (a,b)), "bad gate")
        result.append((a,b))
    require(type(out) is int and -2 <= out < n+len(result), "bad output")
    return tuple(result), out


def decode_chain(obj):
    nodes = tuple(tuple(sequence(node)) for node in sequence(obj["nodes"]))
    roots = tuple(sequence(obj["roots"]))
    steps = []
    for row in sequence(obj["steps"]):
        require(type(row["rule"]) is str, "bad rule name")
        steps.append(Step(context=natural(row["context"]), left=natural(row["left"]),
                          right=natural(row["right"]), rule=row["rule"]))
    return Chain(nodes, roots, tuple(steps))


def verify_result(n, F, S, bound, result, learner):
    """Return True or raise ValueError on a malformed or false certificate."""
    try:
        return _verify(n, F, S, bound, result, learner)
    except (IndexError, KeyError, TypeError) as exc:
        raise ValueError("malformed result") from exc


def _verify(n, F, S, bound, result, learner):
    for name, expected in (("n", n), ("S", S), ("bound", bound)):
        require(natural(result[name]) == natural(expected), "public "+name+" mismatch")
    source = circuit(n, F)
    require(circuit(n, result["F"]) == source, "public source mismatch")
    zero = endpoint(n, *source, -1)
    high = endpoint(n, *source, (1 << n)-1)
    history = ()

    def forecast(q):
        require(len(q[0]) <= S, "query exceeds public cap")
        answer = learner(n, S, history, q)
        require(type(answer) in (bool,int) and answer in (0,1), "bad learner output")
        return int(answer)

    for row in sequence(result["history"]):
        raw, label = sequence(row)
        q, label = circuit(n, raw), bit(label)
        require(q == (high if label else zero), "unjustified history label")
        if label:
            require(forecast(zero) == 0, "source trial bypassed an earlier zero mistake")
        require(forecast(q) != label, "history round was not a mistake")
        history += ((q,label),)

    status = result["status"]
    if status == "unsat":
        require(len(history) >= bound+1, "insufficient mistakes for UNSAT")
        return True
    require(len(history) <= bound, "outcome after exhaustion")
    j = natural(result["assignment"])
    require(j.bit_length() <= n, "assignment outside original domain")
    if status == "witness":
        require(evaluate(n, *source, j) == 1, "assignment fails original source")
        return True
    require(status == "fault", "unknown outcome")
    require(evaluate(n, *source, j) == 0, "claimed false crossing is true")
    raw_chain, index = sequence(result["certificate"])
    chain = decode_chain(raw_chain)
    require(natural(index) < len(chain.steps), "invalid step index")
    require(verify_chain(n, *source, j, chain), "invalid primitive rewrite chain")
    for at, mask, expected_bit in ((0,j,1),(-1,j-1,0)):
        q = endpoint(n, *source, mask)
        require(normalize(n,chain.nodes,chain.roots[at]) == q, "bad chain endpoint")
        require(forecast(q) == expected_bit, "missing crossing at claimed index")
    for offset, name, expected_bit in ((0,"left",1),(1,"right",0)):
        q = circuit(n,result[name])
        require(q == normalize(n,chain.nodes,chain.roots[index+offset]), "bad selected root")
        require(bit(result[name+"_bit"]) == expected_bit == forecast(q), "incorrect forecast")
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--learner", required=True)
    args = parser.parse_args()
    if hasattr(sys,"set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    module, sep, name = args.learner.partition(":")
    if not sep:
        parser.error("expected module:callable")
    learner = getattr(importlib.import_module(module),name)
    try:
        data = json.load(sys.stdin)
        pub = data["expected"]
        verify_result(pub["n"],pub["F"],pub["S"],pub["bound"],data["result"],learner)
    except (ValueError, KeyError, TypeError) as exc:
        print(str(exc),file=sys.stderr)
        return 1
    print("verified")
    return 0


if __name__ == "__main__":
    sys.exit(main())

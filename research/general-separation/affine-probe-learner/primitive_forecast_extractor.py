"""Extract an original SAT witness, a bounded-mistake contradiction, or a rewrite fault.

extract(n, (gates, output), S, bound, learner) forwards immutable circuits and
histories to learner(n, S, history, query). Each call must start in the state
specified by the history. The UNSAT conclusion assumes the stated mistake
bound for that learner, n and S, on every fixed-assignment stream. The caller
can use primitive_rewrite_chain.public_cap(n, len(gates)) for S. A too-small
cap, faulty symbolic certificate or invalid forecast is an error, never UNSAT.

CLI: python primitive_forecast_extractor.py --learner module:callable < input.json
Input JSON fields: n, F=[gates,output], S, bound. Integer assignments use
MSB-first input numbering. The fault certificate is (Chain, step index) in
Python and [chain object, step index] in JSON. The original F is preserved.
"""
import argparse
from dataclasses import asdict, is_dataclass
import importlib
import json
import sys

from check_primitive_rewrite_chain import verify
from primitive_rewrite_chain import build_chain, endpoint, evaluate, normalize


def replay_adapter(fresh):
    """Adapt a deterministic machine supporting predict(q), observe(q,label).

    fresh(n,S) must return its initial state. Predict then observe is one
    complete round. A speculative last prediction is discarded with its clone.
    """
    def forecast(n, cap, history, query):
        machine = fresh(n, cap)
        for prior, label in history:
            machine.predict(prior)
            machine.observe(prior, label)
        return machine.predict(query)
    return forecast


def _natural(x, name):
    if type(x) is not int or x < 0:
        raise ValueError(f"{name} must be a nonnegative integer")
    return x


def _source(n, source):
    if type(source) not in (tuple, list) or len(source) != 2:
        raise ValueError("source must contain a gate list and output")
    gates, output = source
    if type(gates) not in (tuple, list) or any(type(pair) not in (tuple, list) for pair in gates):
        raise ValueError("gates must be an ordered list of NAND pairs")
    gates = tuple(tuple(pair) for pair in gates)
    for i, pair in enumerate(gates):
        if len(pair) != 2 or any(type(w) is not int or not -2 <= w < n + i for w in pair):
            raise ValueError("invalid NAND gate")
    if type(output) is not int or not -2 <= output < n + len(gates):
        raise ValueError("invalid source output")
    return gates, output


def _json(value):
    def convert(obj):
        if is_dataclass(obj):
            return asdict(obj)
        raise TypeError(f"cannot serialize {type(obj).__name__}")
    return json.dumps(value, default=convert, ensure_ascii=True, separators=(",", ":"))


def extract(n, F, S, bound, learner):
    """Run the extractor. 'cost' measures explicit compact ASCII JSON traffic.

    state_bits counts the final labeled replay list. forecast_input_bits counts
    exactly all serialized [n,S,history,query] inputs. Output bits are forecast
    calls (one Boolean each). replay_rounds counts committed rounds replayed
    across all calls when replay_adapter is used. Method-internal costs depend
    on the supplied learner and are additional to these interface measurements.
    """
    _natural(n, "n")
    _natural(S, "S")
    _natural(bound, "bound")
    gates, output = _source(n, F)
    history = ()
    calls = 0
    traffic = 0
    replays = 0

    def forecast(q):
        nonlocal calls, traffic, replays
        if len(q[0]) > S:
            raise ValueError("forecast circuit exceeds the public NAND cap")
        calls += 1
        traffic += 8 * len(_json((n, S, history, q)))
        replays += len(history)
        bit = learner(n, S, history, q)
        if type(bit) not in (bool, int) or bit not in (0, 1):
            raise ValueError("learner returned an invalid forecast")
        return int(bit)

    def result(status, **payload):
        cost = dict(forecast_calls=calls, replay_rounds=replays,
                    forecast_input_bits=traffic, state_bits=8 * len(_json(history)))
        return dict(status=status, n=n, F=(gates, output), S=S, bound=bound,
                    history=history, cost=cost, **payload)

    top = (1 << n) - 1
    low_query = endpoint(n, gates, output, -1)
    high_query = endpoint(n, gates, output, top)
    while True:
        if forecast(low_query):
            history += ((low_query, 0),)
        elif not forecast(high_query):
            history += ((high_query, 1),)
        else:
            break
        if len(history) > bound:
            return result("unsat")

    lo, hi = -1, top
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if forecast(endpoint(n, gates, output, mid)):
            hi = mid
        else:
            lo = mid
    if evaluate(n, gates, output, hi):
        return result("witness", assignment=hi)

    chain = build_chain(n, gates, output, hi)
    if not verify(n, gates, output, hi, chain):
        raise ValueError("invalid false-crossing rewrite chain")
    def presented(index):
        return normalize(n, chain.nodes, chain.roots[index])
    a, b = 0, len(chain.steps)
    if (a == b or presented(a) != endpoint(n, gates, output, hi)
            or presented(b) != endpoint(n, gates, output, lo)):
        raise ValueError("chain does not connect the forecast endpoints")
    # In descending prefix order the endpoint forecasts are 1 then 0.
    while b - a > 1:
        mid = (a + b) // 2
        if forecast(presented(mid)):
            a = mid
        else:
            b = mid
    left, right = presented(a), presented(b)
    if (forecast(left), forecast(right)) != (1, 0):
        raise ValueError("forecasts changed on deterministic replay")
    return result("fault", assignment=hi, left=left, right=right,
                  left_bit=1, right_bit=0, certificate=(chain, a))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--learner", required=True, metavar="MODULE:CALLABLE")
    args = parser.parse_args()
    module, separator, name = args.learner.partition(":")
    if not separator or not name:
        parser.error("expected MODULE:CALLABLE")
    learner = getattr(importlib.import_module(module), name)
    data = json.load(sys.stdin)
    answer = extract(data["n"], data["F"], data["S"], data["bound"], learner)
    print(_json(answer))


if __name__ == "__main__":
    main()

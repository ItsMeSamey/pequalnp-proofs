"""End-to-end extractor replays on two original input bits."""
from check_primitive_rewrite_chain import verify
from primitive_forecast_extractor import extract, replay_adapter
from primitive_rewrite_chain import normalize, public_cap


N = 2
SOURCE = (((0, 0),), 2)  # NOT of the most significant bit
ZERO = ((), -1)


def value(query, assignment):
    gates, out = query
    wires = {-1: 0, -2: 1, 0: assignment >> 1, 1: assignment & 1}
    for i, (a, b) in enumerate(gates, N):
        wires[i] = 1 - wires[a] * wires[b]
    return wires[out]


def majority(history, query):
    live = [x for x in range(4)
            if all(value(old, x) == bit for old, bit in history)]
    return int(2 * sum(value(query, x) for x in live) > len(live))


def run(source, bound, policy):
    cap = public_cap(N, len(source[0]))
    calls = []

    def learner(n, s, history, query):
        assert (n, s) == (N, cap)
        assert isinstance(history, tuple)
        assert len(query[0]) <= cap
        bit = policy(history, query)
        calls.append((history, query, bit))
        return bit

    result = extract(N, source, cap, bound, learner)
    history = result["history"]
    assert history
    for i, (old, label) in enumerate(history):
        assert (history[:i], old, 1 - label) in calls
        assert policy(history[:i], old) == 1 - label
    assert result["cost"]["forecast_calls"] == len(calls)
    assert result["cost"]["replay_rounds"] == sum(len(h) for h, _, _ in calls)
    return result, calls


def main():
    assert [value(SOURCE, x) for x in range(4)] == [1, 1, 0, 0]
    witness, _ = run(SOURCE, 2, majority)
    assert witness["status"] == "witness"
    x = witness["assignment"]
    assert x in (0, 1)
    assert all(value(q, x) == b for q, b in witness["history"])

    impossible, _ = run(ZERO, 2, majority)
    assert impossible["status"] == "unsat"
    assert len(impossible["history"]) == 3
    assert not any(all(value(q, x) == b for q, b in impossible["history"])
                   for x in range(4))

    def syntactic(history, query):
        if not history:
            return 0
        if len(history) == 1:
            return int(query == SOURCE)
        return majority(history, query)

    # At most two initial mistakes plus two majority mistakes on any
    # realizable stream. At the frozen state only the bare source predicts 1.
    fault, calls = run(SOURCE, 4, syntactic)
    assert fault["status"] == "fault"
    assert fault["history"] == ((SOURCE, 1),)
    j = fault["assignment"]
    assert j == 3 and value(SOURCE, j) == 0
    left, right = fault["left"], fault["right"]
    chain, index = fault["certificate"]
    assert verify(N, *SOURCE, j, chain)
    assert 0 <= index < len(chain.steps)
    assert (left, right) == tuple(
        normalize(N, chain.nodes, root) for root in chain.roots[index:index + 2])
    assert {fault["left_bit"], fault["right_bit"]} == {0, 1}
    for query, bit in ((left, fault["left_bit"]), (right, fault["right_bit"])):
        assert (fault["history"], query, bit) in calls
        assert syntactic(fault["history"], query) == bit
    assert all(value(left, x) == value(right, x) for x in range(4))

    machines = []

    class Machine:
        def __init__(self, n, cap):
            assert (n, cap) == (N, fault["S"])
            self.history = ()
            self.events = []
            machines.append(self)

        def predict(self, query):
            self.events.append(("predict", query))
            return syntactic(self.history, query)

        def observe(self, query, label):
            assert self.events[-1] == ("predict", query)
            self.events.append(("observe", query, label))
            self.history += ((query, label),)

    replayed = extract(N, SOURCE, fault["S"], 4, replay_adapter(Machine))
    assert replayed == fault
    assert len(machines) == len(calls)
    for machine, (history, query, _) in zip(machines, calls):
        expected = []
        for prior, label in history:
            expected.extend([("predict", prior), ("observe", prior, label)])
        assert machine.history == history
        assert machine.events == expected + [("predict", query)]


if __name__ == "__main__":
    main()

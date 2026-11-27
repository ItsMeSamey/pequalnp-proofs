"""Exact marker-byte annotations and total scheduled raw pushdown predictors."""
from padding_cnf import encode
from stack_padding import padding_dag
from stack_alias import _slots


def annotated_dag(challenge, n, aliases):
    """Return (edges,start,final,events); events read actual signed marker bytes."""
    slots = _slots(aliases, n)
    positions = {}
    for i, (name, _) in enumerate(slots):
        positions.setdefault(name, []).append(i)
    if any(len(group) > 2 for group in positions.values()):
        raise ValueError("only singleton and paired aliases are supported")
    kinds = {}
    stack = []
    for i, (name, _) in enumerate(slots):
        group = positions[name]
        if len(group) == 1:
            continue
        if group[0] == i:
            kinds[i] = "open"
            stack.append(name)
        elif stack.pop() == name:
            kinds[i] = "close"
        else:
            raise ValueError("crossing alias intervals")
    edges, start, final = padding_dag(challenge, n)
    outgoing = {}
    for j, (u, byte, _) in enumerate(edges):
        outgoing.setdefault(u, []).append((j, byte))
    forks = sorted(u for u, arcs in outgoing.items() if len(arcs) == 2)
    if len(forks) != len(slots):
        raise AssertionError("unexpected number of marker forks")
    events = {}
    for i, u in enumerate(forks):
        arcs = outgoing[u]
        if sum(byte == 45 for _, byte in arcs) != 1 or any(
            byte != 45 and not 49 <= byte <= 57 for _, byte in arcs
        ):
            raise AssertionError("invalid first marker byte")
        if i in kinds:
            name, offset = slots[i]
            for j, byte in arcs:
                events[j] = (kinds[i], name, int(byte == 45) ^ offset)
    return edges, start, final, events


def _comparator(challenge, actions):
    """Total line scanner. A mismatch sets a sticky bit and still pops the frame."""
    first = encode(challenge, len(actions) - 1, 0).count(b"\n") - len(actions)
    finished = first + 2 * len(actions)
    sink = 2 * (finished + 1)
    outputs = {q: int(q == 2 * finished) for q in range(sink + 1)}
    table = {}
    for q in range(sink + 1):
        stage, bad = divmod(q, 2)
        for top in (0, 1, 2):
            for byte in range(256):
                if q == sink or stage == finished:
                    rule = (sink, "stay")
                elif stage < first or (stage - first) % 2:
                    rule = (2 * (stage + int(byte == 10)) + bad, "stay")
                elif byte != 45 and not 49 <= byte <= 57:
                    rule = (sink, "stay")
                else:
                    action = actions[(stage - first) // 2]
                    bit = int(byte == 45)
                    next_state = 2 * (stage + 1)
                    if action == "push":
                        rule = (next_state + bad, "push", bit + 1)
                    elif action == "pop" and top:
                        rule = (next_state + int(bad or top != bit + 1), "pop")
                    elif action == "pop":
                        rule = (sink, "stay")
                    elif action == "gate":
                        rule = (next_state + int(bad or not bit), "stay")
                    else:
                        rule = (next_state + bad, "stay")
                table[q, top, byte] = rule
    return table, 0, 0, outputs


def aligned_fixture(h, *, mismatch=False, gate=True):
    """Return challenge,n,aliases,table,initial,bottom,outputs, with h nested pairs."""
    if type(h) is not int or h < 1 or type(mismatch) is not bool or type(gate) is not bool:
        raise ValueError("expected positive depth and Boolean options")
    challenge = []
    aliases = list(range(1, h + 1)) + list(range(h, 0, -1)) + [h + 1]
    if mismatch:
        aliases[h] = -aliases[h]
    actions = ["push"] * h + ["pop"] * h + ["gate" if gate else "ignore"]
    return challenge, 2 * h, aliases, *_comparator(challenge, actions)


def hostile_fixture(h):
    """Native stack compares C=reverse(A); aliases require D=reverse(B); enable gates."""
    if type(h) is not int or h < 1:
        raise ValueError("expected positive block length")
    challenge = []
    a = list(range(1, h + 1))
    b = list(range(h + 1, 2 * h + 1))
    c = list(range(2 * h + 1, 3 * h + 1))
    aliases = a + b + c + list(reversed(b)) + [3 * h + 1]
    actions = ["push"] * h + ["ignore"] * h + ["pop"] * h + ["ignore"] * h + ["gate"]
    return challenge, 4 * h, aliases, *_comparator(challenge, actions)

"""Physical disagreement with automatic partial-2-tree/apex decomposition."""
from math import prod
import event_csp
import event_decompose
import event_tree
from stack_alias import _slots, decode_alias
from stack_align_pins import _fixed


def solve(challenge, n, aliases, table, initial, bottom, outputs, *, backend="macro",
          schedule=None, occurrence_pins=(), id_pins=(), state_cap=None, step_cap=None):
    """Compute attainable outputs; unsupported schedules, graphs and DP caps give unknown.

    Raw schedules use byte indices. Macro schedules specify the first-byte
    operation of each marker and require all remaining marker bytes to stay.
    """
    if backend not in ("macro", "raw"):
        raise ValueError("backend must be macro or raw")
    for cap in (state_cap, step_cap):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("caps must be nonnegative integers")
    slots = _slots(aliases, n)
    fixed, conflict = _fixed(slots, occurrence_pins, id_pins)
    challenge = tuple(tuple(clause) for clause in challenge)
    table = {key: tuple(action) for key, action in table.items()}
    outputs = dict(outputs)
    metrics = dict(backend=backend, vertices=0, edges=0, bags=0, apex=None,
                   compiler={}, decomposition_attempts=0, width=None,
                   domain_records=0, domain_records_post=0, max_domain_pre=0,
                   max_domain_post=0, candidate_pairs=0, retained_pairs=0,
                   bag_row_bound=None, states=0, steps=0, replay_bytes=0)
    def result(status, **fields):
        return dict(status=status, samples=[], metrics=metrics, **fields)

    if backend == "macro":
        import event_macro
        builder = event_macro.build
    else:
        builder = event_csp.build
    try:
        events = builder(challenge, n, slots, table, initial, bottom, outputs, schedule=schedule)
    except event_csp.ScheduleMismatch as exc:
        return result("unknown", reason=str(exc))

    before = events.domains
    domains = dict(before)
    for at, (name, offset) in zip(events.slot_events, slots):
        if name in fixed:
            bit = fixed[name] ^ offset
            domains[at] = tuple(record for record in domains[at] if record.bit == bit)
    if conflict:
        domains[events.output] = ()
    metrics.update(vertices=len(domains), edges=len(events.edges),
                   compiler=dict(getattr(events, "metrics", {})),
                   max_domain_pre=max(map(len, before.values())),
                   max_domain_post=max(map(len, domains.values())),
                   domain_records=sum(map(len, before.values())),
                   domain_records_post=sum(map(len, domains.values())),
                   candidate_pairs=sum(len(before[u])*len(before[v]) for u,v in events.edges),
                   retained_pairs=sum(len(rel) for _,_,rel in events.constraints))
    if conflict:
        return result("empty")
    decomposition = event_decompose.decompose(domains, events.edges)
    metrics["decomposition_attempts"] = decomposition["attempts"]
    if decomposition["status"] != "ok":
        return result("unknown", reason=decomposition["reason"])
    bags = decomposition["bags"]
    metrics.update(apex=decomposition["apex"], bags=len(bags), width=decomposition["width"],
                   bag_row_bound=sum(prod(len(domains[v]) for v in bag) for bag in bags))
    answer = event_tree.solve(domains, events.constraints, bags, decomposition["tree_edges"],
                              events.output, state_cap=state_cap, step_cap=step_cap)
    metrics.update(states=answer["states"], steps=answer["steps"], width=answer["width"])
    final = result(answer["status"])
    for field in ("value", "reason"):
        if field in answer:
            final[field] = answer[field]
    for bit, witness in sorted(answer["witnesses"].items()):
        try:
            sample = events.replay(witness)
            raw = sample["physical"]
            actual_n, clauses, key, underlying = decode_alias(raw, slots)
            if (actual_n != n or tuple(clauses) != challenge or sample["key"] != key or
                    sample["underlying"] != underlying or sample["prediction"] != bit or
                    any(underlying[name] != pinned for name, pinned in fixed.items())):
                raise ValueError("original source or pin mismatch")
            state = initial
            stack = [bottom]
            for byte in raw:
                action = table[state, stack[-1], byte]
                state = action[0]
                if action[1] == "push":
                    stack.append(action[2])
                elif action[1] == "pop":
                    if len(stack) == 1:
                        raise ValueError("bottom pop in original table")
                    stack.pop()
            if outputs[state] != bit:
                raise ValueError("original table output mismatch")
            metrics["replay_bytes"] += len(raw)
        except (KeyError, ValueError) as exc:
            return result("unknown", reason="physical replay failed: " + str(exc))
        final["samples"].append(sample)
    return final

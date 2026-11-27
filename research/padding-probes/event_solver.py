"""Evaluate and physically replay a visible byte-event CSP on a supplied tree."""
import event_csp
import event_tree
from stack_alias import _slots
from stack_align_pins import _fixed


def solve(challenge, n, aliases, table, initial, bottom, outputs, bags, tree_edges,
          *, schedule=None, occurrence_pins=(), id_pins=(), state_cap=None, step_cap=None):
    slots = _slots(aliases, n)
    fixed, conflict = _fixed(slots, occurrence_pins, id_pins)
    for cap in (state_cap, step_cap):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError('nonnegative cap required')
    metrics = dict(max_domain_pre=None, max_domain_post=None, domain_records=None,
                   domain_records_post=None, candidate_pairs=None, retained_pairs=None,
                   width=None, states=0, steps=0)

    def unknown(reason):
        return dict(status='unknown', reason=reason, samples=[], metrics=metrics)

    try:
        events = event_csp.build(challenge, n, slots, table, initial, bottom, outputs,
                                 schedule=schedule)
    except event_csp.ScheduleMismatch as exc:
        return unknown(str(exc))
    domains = events.domains.copy()
    for index, (name, offset) in zip(events.slot_events, slots):
        if name in fixed:
            bit = fixed[name] ^ offset
            domains[index] = tuple(row for row in domains[index] if row.bit == bit)
    if conflict:
        domains[events.output] = ()
    before = events.domains
    metrics.update(max_domain_pre=max(map(len, before.values())),
                   max_domain_post=max(map(len, domains.values())),
                   domain_records=sum(map(len, before.values())),
                   domain_records_post=sum(map(len, domains.values())),
                   candidate_pairs=sum(len(before[u]) * len(before[v]) for u, v in events.edges),
                   retained_pairs=sum(len(relation) for _, _, relation in events.constraints))
    try:
        answer = event_tree.solve(domains, events.constraints, bags, tree_edges, events.output,
                                  state_cap=state_cap, step_cap=step_cap)
    except (TypeError, ValueError) as exc:
        return unknown('invalid decomposition: ' + str(exc))
    for field in ('width', 'states', 'steps'):
        metrics[field] = answer[field]
    samples = []
    for bit, witness in sorted(answer['witnesses'].items()):
        try:
            sample = events.replay(witness)
        except ValueError as exc:
            return unknown('physical replay failed: ' + str(exc))
        if (sample['prediction'] != bit or conflict or
                any(sample['underlying'].get(name) != value for name, value in fixed.items())):
            return unknown('physical replay disagrees with output or pins')
        samples.append(sample)
    result = dict(status=answer['status'], samples=samples, metrics=metrics)
    for field in ('value', 'reason'):
        if field in answer:
            result[field] = answer[field]
    return result

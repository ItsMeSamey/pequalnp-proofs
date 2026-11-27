"""Count original physical words by Gaussian inclusion-exclusion and replay witnesses."""
from dataclasses import dataclass
from types import MappingProxyType
import event_csp
import event_affine_ie
from stack_alias import _slots, decode_alias
from stack_align_pins import _fixed


@dataclass(frozen=True)
class CodebookView:
    domains: object
    constraints: tuple
    edges: tuple
    output: int
    slot_events: tuple


def solve(challenge, n, aliases, table, initial, bottom, outputs, *, backend="macro",
          schedule=None, occurrence_pins=(), id_pins=(), codebooks=None, omission_cap=None, branch_cap=None):
    """Use a supplied codebook mapping or call a factory on a read-only unpinned view.

    The factory returns the same partial vertex -> record -> integer mapping.
    Its runtime is additional to preprocessing and the branch cap.
    """
    if backend not in ("macro", "raw"):
        raise ValueError("backend must be macro or raw")
    for cap in (omission_cap, branch_cap):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("caps must be nonnegative integers")
    slots = _slots(aliases, n)
    fixed, conflict = _fixed(slots, occurrence_pins, id_pins)
    challenge = tuple(tuple(clause) for clause in challenge)
    table = {key: tuple(action) for key, action in table.items()}
    outputs = dict(outputs)
    metrics = dict(backend=backend, vertices=0, edges=0, compiler={}, gaussian={},
                   codebook_factory=callable(codebooks), supplied_codebooks=0,
                   supplied_codewords=0, max_supplied_code_bits=0, domain_records=0,
                   domain_records_post=0, max_domain_pre=0, max_domain_post=0,
                   candidate_pairs=0, retained_pairs=0, replay_bytes=0)
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
        return result("empty", counts={0:0, 1:0})
    if callable(codebooks):
        view = CodebookView(MappingProxyType({v:tuple(d) for v,d in before.items()}),
                            tuple((u,v,frozenset(rel)) for u,v,rel in events.constraints),
                            tuple(events.edges), events.output, tuple(events.slot_events))
        codebooks = codebooks(view)
    if codebooks is not None:
        codebooks = {v:dict(book) for v,book in codebooks.items()}
        for v,book in codebooks.items():
            if v not in before or any(record not in before[v] for record in book):
                raise ValueError("unknown vertex or original record in codebook")
            words=list(book.values())
            if any(type(word) is not int or word<0 for word in words) or len(set(words))!=len(words):
                raise ValueError("codewords must be injective nonnegative integers")
        metrics.update(supplied_codebooks=len(codebooks),
                       supplied_codewords=sum(len(book) for book in codebooks.values()),
                       max_supplied_code_bits=max((w.bit_length() for book in codebooks.values()
                                                  for w in book.values()),default=0))
    answer = event_affine_ie.solve(domains, events.constraints, events.output,
                                        codebooks=codebooks, omission_cap=omission_cap,
                                        branch_cap=branch_cap)
    metrics["gaussian"] = answer["metrics"]
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
    if answer["status"] in ("pair", "constant", "empty"):
        if "counts" not in answer or set(answer["counts"])-{0,1}:
            return result("unknown", reason="incomplete count certificate")
        counts = {bit: answer["counts"].get(bit,0) for bit in (0,1)}
        if any(type(c) is not int or c<0 for c in counts.values()):
            return result("unknown", reason="invalid physical count")
        positive = {bit for bit,c in counts.items() if c}
        expected = 1 << (len({name for name,_ in slots}) - len(fixed))
        if (sum(counts.values()) != expected or positive != set(answer["witnesses"]) or
                answer["status"] != ("empty","constant","pair")[len(positive)]):
            return result("unknown", reason="physical count or support mismatch")
        final["counts"] = counts
    return final

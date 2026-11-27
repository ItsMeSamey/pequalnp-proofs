"""Sparse single-stack product for a byte DAG with nested paired aliases.

The caller certifies that each complete raw path has the same paired schedule,
that each alias occurs once at its open and once at its close, and that the bit
on each event is the logical value after accounting for the slot's polarity.
"""
from collections import defaultdict, deque


class _Capped(Exception):
    pass


def probe(edges, start, final, table, initial, bottom, outputs, events, *,
          predict=None, fact_cap=None, step_cap=None, promised=False):
    """Find two terminal outputs, or certify a constant under table fidelity.

    Edges are (u, byte, v), u<v. A table entry keyed by (state,top,byte)
    is (next,'stay'), (next,'pop'), or (next,'push',symbol). A top frame
    persists until popped. Terminal output depends only on the control.
    """
    edges = tuple(edges)
    events = dict(events)
    for i, (kind, alias, bit) in events.items():
        if type(i) is not int or not 0 <= i < len(edges):
            raise ValueError('invalid event edge')
        if kind not in ('open', 'close') or type(bit) is not int or bit not in (0, 1):
            raise ValueError('invalid alias event')
        hash(alias)
    outgoing = defaultdict(list)
    alphabet = set()
    if any(type(v) is not int for v in (start, final)):
        raise ValueError('integer endpoints required')
    for index, (u, byte, v) in enumerate(edges):
        if type(u) is not int or type(v) is not int or u >= v:
            raise ValueError('vertex numbering must be topological')
        if type(byte) is not int or not 0 <= byte < 256:
            raise ValueError('invalid byte')
        outgoing[u].append((index, byte, v))
        alphabet.add(byte)
    if initial not in outputs or any(bit not in (0, 1) for bit in outputs.values()):
        raise ValueError('invalid output function')
    symbols = {bottom}
    for (state, top, byte), action in table.items():
        symbols.add(top)
        if state not in outputs or type(byte) is not int or not 0 <= byte < 256:
            raise ValueError('invalid transition source')
        if len(action) < 2 or action[0] not in outputs:
            raise ValueError('invalid transition target')
        if action[1] == 'push' and len(action) == 3 and action[2] != bottom:
            symbols.add(action[2])
        elif len(action) != 2 or not (action[1] == 'stay' or
                                      (action[1] == 'pop' and top != bottom)):
            raise ValueError('invalid stack operation')
    for state in outputs:
        for symbol in symbols:
            if any((state, symbol, byte) not in table for byte in alphabet):
                raise ValueError('table incomplete on graph alphabet')
    for cap in (fact_cap, step_cap):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError('nonnegative cap required')

    # Local paths keep their entry frame alive. Return paths include its pop.
    # A waiter remembers the caller and its path through the pushing edge.
    root = (start, initial, bottom, None)
    prefixes = {root: None}
    local = set()
    waiters = defaultdict(dict)
    returns = defaultdict(dict)
    agenda = deque()
    samples = {}
    facts = steps = 0

    def charge_fact():
        nonlocal facts
        if fact_cap is not None and facts >= fact_cap:
            raise _Capped
        facts += 1

    def step():
        nonlocal steps
        if step_cap is not None and steps >= step_cap:
            raise _Capped
        steps += 1

    # Ropes share provenance of retained facts. None denotes an empty path.
    def join(left, right):
        if left is None:
            return right
        if right is None:
            return left
        return (left, right)

    def add(entry, vertex, state, path):
        key = entry, vertex, state
        if key not in local:
            charge_fact()
            local.add(key)
            agenda.append((entry, vertex, state, path))

    def sample(rope, output):
        work = [rope]
        path = []
        while work:
            node = work.pop()
            if type(node) is tuple:
                left, right = node
                work.extend((right, left))
            elif node is not None:
                path.append(node)
        live_marks = []
        seen = set()
        for i in path:
            event = events.get(i)
            if event is None:
                continue
            kind, alias, bit = event
            if kind == 'open':
                if alias in seen:
                    return None
                seen.add(alias)
                live_marks.append((alias, bit))
            elif not live_marks or live_marks.pop() != (alias, bit):
                return None
        if live_marks:
            return None
        raw = bytes(edges[i][1] for i in path)
        observed = output if predict is None else predict(raw)
        if type(observed) not in (bool, int) or observed not in (0, 1):
            raise ValueError('predict must return a bit')
        return dict(path=path, physical=raw, prediction=int(observed), table_output=output)

    def result(status, **extra):
        return dict(status=status, samples=list(samples.values()),
                    facts=facts, steps=steps, **extra)

    try:
        add(root, start, initial, None)
        while agenda:
            entry, u, state, path = agenda.popleft()
            if u == final:
                bit = int(outputs[state])
                if bit not in samples:
                    witness = sample(join(prefixes[entry], path), bit)
                    if witness is None:
                        return result('unaligned', reason='witness schedule mismatch')
                    samples[bit] = witness
                    if samples[bit]['prediction'] != bit:
                        return result('unknown', reason='prediction mismatch')
                    if len(samples) == 2:
                        return result('pair')
                continue
            for index, byte, v in outgoing.get(u, ()):
                step()
                action = table[state, entry[2], byte]
                target, op = action[:2]
                event = events.get(index)
                pushed_mark = None
                if event is not None:
                    kind, alias, bit = event
                    if kind == 'open':
                        if op != 'push':
                            return result('unaligned', reason='open requires push', edge=index)
                        pushed_mark = (alias, bit)
                    else:
                        mark = entry[3]
                        if mark is None or mark[0] != alias:
                            return result('unaligned', reason='wrong frame at close', edge=index)
                        # The edge cannot extend an alias-consistent path. Its
                        # predictor action is irrelevant, even if it would stay.
                        if mark[1] != bit:
                            continue
                        if op != 'pop':
                            return result('unaligned', reason='close requires pop', edge=index)
                elif op == 'pop' and entry[3] is not None:
                    return result('unaligned', reason='untagged pop of alias', edge=index)
                extended = join(path, index)
                if op == 'stay':
                    add(entry, v, target, extended)
                elif op == 'push':
                    child = (v, target, action[2], pushed_mark)
                    if child not in prefixes:
                        prefixes[child] = join(prefixes[entry], extended)
                        add(child, v, target, None)
                    if entry not in waiters[child]:
                        charge_fact()
                        waiters[child][entry] = extended
                        for (w, q), suffix in returns[child].items():
                            step()
                            add(entry, w, q, join(extended, suffix))
                elif (v, target) not in returns[entry]:
                    charge_fact()
                    returns[entry][v, target] = extended
                    for caller, prefix in waiters[entry].items():
                        step()
                        add(caller, v, target, join(prefix, extended))
    except _Capped:
        return result('unknown', reason='cap')
    if not samples:
        return result('empty')
    if promised:
        return result('constant', value=next(iter(samples)))
    return result('unknown', reason='representation unpromised')

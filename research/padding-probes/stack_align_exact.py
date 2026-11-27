"""Universal synchronization on the canonical, pin-propagated paired slot chart.

The caller certifies that each complete raw path has the same paired schedule,
that each alias occurs once at its open and once at its close, and that the bit
on each event is the logical value after accounting for the slot's polarity.
"""
from collections import defaultdict, deque
from stack_align_pins import complete_edge_prefix


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
    root = (start, (initial, None), bottom, None)
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

    def flatten(rope):
        work = [rope]
        path = []
        while work:
            node = work.pop()
            if type(node) is tuple:
                left, right = node
                work.extend((right, left))
            elif node is not None:
                path.append(node)
        return path

    def sample(rope, output):
        path = flatten(rope)
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

    def replay(full):
        # The completed alias word must be legal independently of synchronization.
        pending = []
        seen = set()
        vertex = start
        frames = [(bottom, None)]
        state = initial
        first = None
        for pos, i in enumerate(full):
            u, byte, vertex_next = edges[i]
            if u != vertex:
                return False, None
            vertex = vertex_next
            event = events.get(i)
            mark = None
            if event is not None:
                kind, alias, bit = event
                mark = (alias, bit)
                if kind == 'open':
                    if alias in seen:
                        return False, None
                    seen.add(alias)
                    pending.append(mark)
                elif not pending or pending.pop() != mark:
                    return False, None
            if first is not None:
                continue
            top, frame_mark = frames[-1]
            action = table[state, top, byte]
            state, op = action[:2]
            if event is None:
                wrong = op == 'pop' and frame_mark is not None
            elif kind == 'open':
                wrong = op != 'push'
            else:
                wrong = op != 'pop' or frame_mark != mark
            if wrong:
                first = pos
            elif op == 'push':
                frames.append((action[2], mark))
            elif op == 'pop':
                frames.pop()
        return vertex == final and not pending, first

    def bad(reason, entry, path, index):
        prefix = flatten(join(prefixes[entry], join(path, index)))
        full = complete_edge_prefix(edges, start, final, events, prefix)
        if full is None or list(full[:len(prefix)]) != prefix:
            return result('unknown', reason='canonical completion failed')
        if replay(full) != (True, len(prefix) - 1):
            return result('unknown', reason='first mismatch replay failed')
        witness = dict(physical=bytes(edges[i][1] for i in full), path=list(full),
                       prefix_path=prefix, edge=index)
        return result('unaligned', reason=reason, witness=witness, edge=index, synchronized=False)

    try:
        add(root, start, (initial, None), None)
        while agenda:
            entry, u, control, path = agenda.popleft()
            state, cache = control
            if u == final:
                bit = int(outputs[state])
                if bit not in samples:
                    witness = sample(join(prefixes[entry], path), bit)
                    if witness is None:
                        return result('unknown', reason='witness schedule mismatch')
                    samples[bit] = witness
                continue
            for index, byte, v in outgoing.get(u, ()):
                step()
                action = table[state, entry[2], byte]
                target, op = action[:2]
                event = events.get(index)
                pushed_mark = None
                next_cache = cache
                if event is not None:
                    kind, alias, bit = event
                    if kind == 'open':
                        if op != 'push':
                            return bad('open requires push', entry, path, index)
                        pushed_mark = (alias, bit, cache)
                        next_cache = (alias, bit)
                    else:
                        if cache is None or cache[0] != alias:
                            return result('unknown', reason='invalid canonical close schedule')
                        if cache[1] != bit:
                            continue
                        mark = entry[3]
                        if mark is None or mark[:2] != cache:
                            return bad('wrong frame at close', entry, path, index)
                        if op != 'pop':
                            return bad('close requires pop', entry, path, index)
                        next_cache = mark[2]
                elif op == 'pop' and entry[3] is not None:
                    return bad('untagged pop of alias', entry, path, index)
                target = (target, next_cache)
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
    if any(row['prediction'] != bit for bit, row in samples.items()):
        return result('unknown', reason='prediction mismatch', synchronized=True)
    if len(samples) == 2:
        return result('pair', synchronized=True)
    if not samples:
        return result('empty', synchronized=True)
    if promised:
        return result('constant', value=next(iter(samples)), synchronized=True)
    return result('unknown', reason='representation unpromised', synchronized=True)

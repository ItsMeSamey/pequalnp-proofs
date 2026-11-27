"""All physical mixed-root histories. Cache only extension shapes, never connectivity."""
from collections import Counter, defaultdict
from types import SimpleNamespace
from degree_five_active_shells import root, grow, key, glue
from mixed_edge_torso_shells import roots
import degree_five_terminal_sweep as terminal_module


def terminal_shapes(degrees, table):
    k = len(degrees)
    f = (1 << k) - 1
    actual_drift = sum((1 ^ (d & 1)) << i for i, d in enumerate(degrees))
    ok = []
    for drift, row in enumerate(table):
        entries = []
        for u, count in row.items():
            full = u == f and drift == actual_drift
            if full:
                entries.append((f, u))
            if count > int(full):
                entries.append((0, u))
        ok.append(entries)
    fake = SimpleNamespace(rows=[0]*k, ports=range(k), degrees=degrees, ok=ok)
    for rows in terminal_module.terminal(fake):
        yield tuple(x & f for x in rows[k:]), tuple(x >> k for x in rows[k:])


def unique_full(rows):
    """Decision tree that checks every partial selection against determined equations."""
    full = (1 << len(rows)) - 1
    def possible(on, off):
        left = full ^ (on | off)
        for v, row in enumerate(rows):
            if on >> v & 1 and not row & left and ((row & on).bit_count() & 1) != (rows[v].bit_count() & 1):
                return False
        if not left:
            return bool(off)
        bit = left & -left
        return possible(on, off | bit) or possible(on | bit, off)
    return not possible(3, 0)


def main():
    connected = terminal_module.three_connected
    # The shape cache has no historical graph; only actual glued rows are checked below.
    terminal_module.three_connected = lambda _: True
    terminal_module.exact_word = lambda _: True
    active = defaultdict(list)
    for old in roots():
        d, tbl = root(dict(rows=old.rows, ports=old.ports))
        active[key(d,tbl)].append((old.rows,old.ports))
    total = Counter()
    examples = {}
    level = 0
    while active:
        next_level = defaultdict(list)
        local = Counter()
        for (ds, tab), histories in active.items():
            table = [dict(row) for row in tab]
            for inc, internal in terminal_shapes(ds, table):
                for rows, ports in histories:
                    rr, _ = glue(rows, ports, inc, internal)
                    rr[0] ^= 1
                    if connected(rr):
                        assert [r.bit_count() for r in rr[:2]] == [4,5]
                        assert all(r.bit_count() in (3,5) for r in rr[2:])
                        assert unique_full(rr)
                        local[len(rr)] += 1
                        examples.setdefault(len(rr),rr)
            for dd, tt, inc, internal in grow(ds,table):
                dest = next_level[key(dd, tt)]
                for rows, ports in histories:
                    dest.append(glue(rows, ports, inc, internal))
        print(level, len(active), sum(map(len,active.values())), sorted(local.items()),flush=True)
        total.update(local)
        active = next_level
        level += 1
    print('total',sorted(total.items()),'examples',examples,flush=True)


if __name__ == '__main__':
    main()

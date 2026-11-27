"""Reduced transition fixtures, not an implementation of the full JMV machine."""
from itertools import product
from jmv_prefix_trie import triples


def label(tag, payload):
    raw = tag + payload
    assert len(raw) <= 12
    return int(raw.ljust(12, '0'), 2)


def clause(case, word):
    row = format(word & 7, '03b')
    sel = word >> 3 & 3
    local = label('00', row + '01')
    conf = label('11', row + '1')
    sorter = lambda typ, w: label('10', '0' + typ + w + '01')
    fetch = lambda w, state: label('01', '00' + w + state)
    left = row[1:] + row[:1]
    flipleft = row[1:] + str(1-int(row[0]))
    right = row[-1] + row[:-1]
    sink = label('01', '11')
    dummy = label('11', '111111')
    if word & 32:
        return ((label('00', '00001'), 1),) * 3
    if case == 'sort-and':
        g = sorter('00', row)
        a = sorter('00', left)
        b = sorter('00', flipleft)
        if sel == 0:
            return ((a, 0), (b, 0), (g, 1))
        if sel == 1:
            return ((g, 0), (a, 1), (a, 1))
        if sel == 2:
            return ((g, 0), (b, 1), (b, 1))
        return ((dummy, 0), (dummy, 1), (dummy, 1))
    if case == 'sort-input':
        g = sorter('01', row)
        child = conf
    elif case == 'local':
        g = local
        child = (conf, sorter('00', row), fetch(format(word & 3, '03b'), '00'),
                 label('00', row + '11'))[sel]
    elif case == 'fetch':
        g = fetch(row, '01')
        child = fetch((row, left, right, format(int(row, 2) & 5, '03b'))[sel], '10')
    elif case == 'sink':
        g = fetch(row, '11')
        child = sink
    else:
        raise ValueError(case)
    # Copy equality uses both polarities. Repetitions pad binary clauses.
    return ((g, sel & 1), (child, 1-(sel & 1)), (child, 1-(sel & 1)))


def localize(values, width):
    axes = [i for i in range(width) if any(
        values[w] != values[w ^ (1 << i)] for w in range(1 << width))]
    table = 0
    for j in range(1 << len(axes)):
        word = sum(((j >> k) & 1) << i for k, i in enumerate(axes))
        table |= values[word] << j
    return tuple(axes), table


def main():
    for case in ('local', 'sort-and', 'sort-input', 'fetch', 'sink'):
        rows = [clause(case, i) for i in range(64)]
        names = [[localize([v[slot][0] >> shift & 1 for v in rows], 6)
                  for shift in range(11, -1, -1)] for slot in range(3)]
        for width in (0, 3, 5, 8):
            expected = {tuple(w >> (12-width) for w, _ in row) for row in rows}
            assert list(triples(6, names, width)) == sorted(expected)
    for a,b,g in product(range(2), repeat=3):
        gates = [clause('sort-and', (j << 3) | 1) for j in range(3)]
        env = dict(zip((gates[0][0][0], gates[0][1][0], gates[0][2][0]), (a,b,g)))
        assert all(any(env[w] == s for w,s in c) for c in gates) == (g == (a & b))
    assert len(set(triples(3, [[((i,),2)] for i in range(3)],1))) == 8
    for bad in [((0,0),0), ((3,),1), ((),2), ((0,),-1)]:
        try:
            list(triples(3, [[bad]]*3, 1))
        except ValueError:
            continue
        raise AssertionError(bad)
    print("Five reduced transition families, ordered prefix covers and signed AND clauses passed.")


if __name__ == '__main__':
    main()

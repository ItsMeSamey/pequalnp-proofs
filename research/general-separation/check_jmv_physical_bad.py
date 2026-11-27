"""Standalone reduced address-decoder fixture and physical Bad/CNF compiler."""
from collections import Counter
from itertools import product

ZERO, ONE = -1, -2
AND, XOR = 8, 6


class Circuit:
    def __init__(self, width):
        self.width = width
        self.gates = []

    def gate(self, table, a, b):
        self.gates.append((table, a, b))
        return self.width + len(self.gates) - 1

    def trace(self, x):
        bits = [x >> i & 1 for i in range(self.width)]
        for table, a, b in self.gates:
            bits.append(table >> (2 * read(bits, a) + read(bits, b)) & 1)
        return bits


def read(bits, wire):
    return bits[wire] if wire >= 0 else int(wire == ONE)


def cnf(c, output):
    clauses = []
    for i, (table, a, b) in enumerate(c.gates, c.width):
        for x, y in product(range(2), repeat=2):
            if any(w < 0 and read([], w) != val for w, val in ((a,x),(b,y))):
                continue
            terms = [(-1 if v else 1)*(w+1) for w,v in ((a,x),(b,y)) if w >= 0]
            terms.append((1 if table >> (2*x+y) & 1 else -1)*(i+1))
            clauses.append(tuple(terms))
    clauses.append((output+1,))
    return clauses


def raw(index):
    row, sub, parity = index & 1, index >> 1 & 1, index >> 2 & 1
    return ((f'0{row}{sub}0', parity), (f'1{row}00', 1),
            (f'0{row}{sub}0', parity))


def decoder():
    # Same typed names as raw(), bit-serialized instead of formatting their values.
    return (((ZERO,0,1,ZERO),2), ((ONE,0,ZERO,ZERO),ONE),
            ((ZERO,0,1,ZERO),2))


def bad(prefixes, patches, baseline):
    c = Circuit(4)  # input bit 3 is unused index filler
    ok = ONE
    defaults = 0
    for prefix, (name, sign) in zip(prefixes, decoder()):
        for literal, wire in zip(prefix, name):
            table = AND if literal == '1' else 4  # ok and NOT wire
            ok = c.gate(table, ok, wire)
        if prefix in patches:
            assert len(prefix) == len(name)
            value = ONE if patches[prefix] else ZERO
        else:
            defaults += 1
            wires = list(name)
            for table, a, b in baseline:
                wires.append(c.gate(table, wires[a], wires[b]))
            value = wires[-1]
        ok = c.gate(AND, ok, c.gate(XOR, value, sign))
    assert len(c.gates) == defaults*len(baseline) + sum(map(len,prefixes)) + 6
    return c, ok


def run():
    patches = {'0000':1, '1100':0}
    # Build the partition from internal paths to account for shared ancestors.
    internal = {n[:i] for n in patches for i in range(len(n))}
    prefixes = {p+b for p in internal for b in '01'} - internal
    baseline = [(XOR,0,1),(XOR,4,2)]
    observed = Counter()
    expected = Counter()
    for x in range(16):
        clause = raw(x)
        end = tuple(next(p for p in prefixes if n.startswith(p)) for n,s in clause)
        observed[end] += 1
        def val(n):
            return patches.get(n, sum(map(int,n[:3])) % 2)
        if all(val(n) != s for n,s in clause):
            expected[end] += 1
    assert sum(expected.values()) > 0 and len(expected) < len(observed)
    for end in list(observed) + [('0000',)*3]:
        c, out = bad(end, patches, baseline)
        clauses = cnf(c, out)
        assert len(clauses) <= 4*len(c.gates)+1 and max(map(len,clauses)) <= 3
        count = 0
        for x in range(16):
            bits = c.trace(x)
            def satisfied(clause):
                return any(bits[abs(lit)-1] == (lit > 0) for lit in clause)
            assert all(map(satisfied,clauses[:-1]))
            count += all(map(satisfied, clauses))
            # First differing gate is forced: flip it, test its own violated row.
            for i in range(4,len(bits)):
                bits[i] ^= 1
                assert any(not satisfied(row) for row in clauses[:-1] if abs(row[-1])==i+1)
                bits[i] ^= 1
        assert count == expected[end]
    print('Physical Bad counts, per-index unique extensions and leaf-size accounting passed.')


if __name__ == '__main__':
    run()

"""Rank-width DP and independent exhaustive node checks for shifted GF(2) guards.

The guards are (x_i + pivot_shift_i)((Ax)_i + offset_i) = 0. The marker
is an arbitrary linear map of x with a prescribed affine target. Bitsets
retain global coordinates for checking cut-effect computations directly.
"""
from collections import defaultdict
from random import Random


def parity(x):
    return x.bit_count() % 2


def bits(mask):
    while mask:
        unit = mask & -mask
        yield unit.bit_length()-1
        mask ^= unit


def image(columns):
    span = {0}
    for column in columns:
        if column not in span:
            span.update([v ^ column for v in span])
    return span


class Instance:
    def __init__(self,rows,marks,pivot_shift,offset):
        self.rows = rows
        self.marks = marks  # Syndrome contributed by each selected bit.
        self.pivot_shift = pivot_shift
        self.offset = offset
        self.full = (1 << len(rows))-1
        self.columns = [sum(1 << j for j,row in enumerate(rows) if row >> i & 1)
                        for i in range(len(rows))]
        assert self.columns == rows

    def incoming(self,scope):
        return image(self.columns[j] & scope for j in bits(self.full ^ scope))

    def state_bound(self,scope):
        incoming = self.incoming(scope)
        outgoing = image(self.columns[j] & ~scope for j in bits(scope))
        assert len(incoming) == len(outgoing)  # transpose cut matrices
        return len(incoming)*len(outgoing)*len(image(self.marks[j] for j in bits(scope)))

    def brute(self,scope):
        # This enumerates full assignments. It does not use the child states,
        # computed column images, or the combination rule.
        outside = self.full ^ scope
        states = set()
        for x in range(self.full+1):
            if any((x ^ self.pivot_shift) >> i & 1
                   and parity(self.rows[i] & x) != (self.offset >> i & 1)
                   for i in bits(scope)):
                continue
            marker = 0
            for i in bits(scope & x):
                marker ^= self.marks[i]
            out = sum(1 << i for i in bits(outside) if parity(self.rows[i] & scope & x))
            inc = sum(1 << i for i in bits(scope) if parity(self.rows[i] & outside & x))
            states.add((marker,out,inc))
        return states

    def leaf(self,i):
        scope = 1 << i
        states = {}
        for inc in self.incoming(scope):
            for value in (0,1):
                x = value << i
                factor = parity(self.rows[i] & x) ^ bool(inc) ^ (self.offset >> i & 1)
                if (value ^ (self.pivot_shift >> i & 1)) and factor:
                    continue
                marker = self.marks[i] if value else 0
                out = self.columns[i] & ~scope if value else 0
                states[marker,out,inc] = x
        return scope,states

    def merge(self,left,right):
        L,left_states = left
        R,right_states = right
        assert not L & R
        scope = L | R
        states = {}
        # Index by the outgoing and incoming cut effects, allowing all labels
        # sharing this key. Children agree on a cut via the effect equations.
        by_left = defaultdict(list)
        by_right = defaultdict(list)
        for (h,o,i),x in left_states.items():
            by_left[o,i].append((h,x))
        for (h,o,i),x in right_states.items():
            by_right[o,i].append((h,x))
        left_out = {o for o,_ in by_left}
        right_out = {o for o,_ in by_right}
        for inc in self.incoming(scope):
            for lo in left_out:
                ri = (inc ^ lo) & R
                for ro in right_out:
                    li = (inc ^ ro) & L
                    ls = by_left.get((lo,li),())
                    rs = by_right.get((ro,ri),())
                    out = (lo ^ ro) & ~scope
                    for lh,lx in ls:
                        for rh,rx in rs:
                            states.setdefault((lh ^ rh,out,inc),lx | rx)
        return scope,states

    def verify(self,table):
        scope,states = table
        assert states.keys() == self.brute(scope)
        assert len(states) <= self.state_bound(scope)
        for (marker,out,inc),x in states.items():
            assert x & ~scope == 0
            h = 0
            for i in bits(x):
                h ^= self.marks[i]
            assert marker == h
            assert out == sum(1 << i for i in bits(self.full ^ scope) if parity(self.rows[i]&x))
            for i in bits(scope):
                if (x ^ self.pivot_shift) >> i & 1:
                    assert parity(self.rows[i]&x) ^ ((inc ^ self.offset) >> i & 1) == 0


def run():
    rng = Random(20261126)
    trials = nodes = states_count = targets = 0
    for n in range(1,9):
        for trial in range(30):
            rows = [0]*n
            threshold = (0,0.15,0.5,0.8,1)[trial%5]
            for i in range(n):
                for j in range(i,n):
                    if rng.random() < threshold:
                        rows[i] |= 1 << j
                        rows[j] |= 1 << i
            marks = [rng.randrange(8) for i in range(n)]
            instance = Instance(rows,marks,rng.randrange(1 << n),rng.randrange(1 << n))
            pool = []
            for i in range(n):
                node = instance.leaf(i)
                instance.verify(node)
                nodes += 1
                states_count += len(node[1])
                pool.append(node)
            while len(pool)>1:
                left = pool.pop(rng.randrange(len(pool)))
                right = pool.pop(rng.randrange(len(pool)))
                node = instance.merge(left,right)
                instance.verify(node)
                nodes += 1
                states_count += len(node[1])
                pool.append(node)
            root = pool[0][1]
            for syndrome in range(8):
                if (syndrome,0,0) in root:
                    x = root[syndrome,0,0]
                    assert all(not((x ^ instance.pivot_shift) >> i & 1) or
                               parity(rows[i]&x) == (instance.offset >> i & 1) for i in range(n))
                targets += 1
            trials += 1
    return trials,nodes,states_count,targets


if __name__ == '__main__':
    t,n,s,h = run()
    print(f"{t} random shifted symmetric systems; {n} exact node tables, {s} witnessed states, {h} root syndrome targets verified.")

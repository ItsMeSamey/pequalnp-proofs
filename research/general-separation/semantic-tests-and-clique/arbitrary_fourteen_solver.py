"""Construct occupancies and per-edge defect bits for two readouts at density 14.

solve(rows, c, edges, labels, target) uses the low-bit-first edge table convention
of general_fourteen_check. Rows are symmetric off the diagonal. Label columns
and target are two-bit vectors. Return (occupancy_mask, defects) or None.
"""
from itertools import combinations, product

from general_fourteen_check import bits, fixed, verify
from module_affine_escape import affine
from role_bipartite_two_marks import mixed


def parity(mask):
    return mask.bit_count() & 1


def component(start, adjacency):
    seen = 1 << start
    queue = [start]
    for site in queue:
        fresh = adjacency[site] & ~seen
        seen |= fresh
        queue.extend(bits(fresh))
    return seen


def directed_type(table):
    for occ in range(1, 4):
        choices = [d for d in range(4) if table >> (4 * occ + d) & 1]
        for end in bits(occ):
            values = {(d >> end) & 1 for d in choices}
            if len(values) == 1:
                return end, 1 ^ ((occ >> (1-end)) & 1), values.pop()
    return None


class Network:
    def __init__(self, rows, c, edges, labels, target):
        self.n = len(rows)
        self.full = (1 << self.n) - 1
        self.edges = edges
        self.labels = labels
        self.target = target
        self.readouts = [
            (sum(((label >> j) & 1) << i for i, label in enumerate(labels)),
             (target >> j) & 1)
            for j in range(2)
        ]
        self.rows = [row & ~(1 << i) for i, row in enumerate(rows)]
        self.offset = c ^ sum((row & (1 << i)) for i, row in enumerate(rows))
        self.releases = [[] for _ in rows]
        self.ordinary = []
        adjacency = [0] * self.n
        heads = 0
        for i, j, table in edges:
            kind = directed_type(table)
            if kind is None:
                self.ordinary.append((i, j, table))
                adjacency[i] |= 1 << j
                adjacency[j] |= 1 << i
            else:
                end, release, baseline = kind
                tail, head = (i, j) if end == 0 else (j, i)
                self.releases[tail].append((head, release))
                self.offset ^= baseline << tail
                heads |= 1 << head
        self.group = [0] * self.n
        self.U = self.singletons = 0
        for i in range(self.n):
            if self.group[i]:
                continue
            group = component(i, adjacency)
            for v in bits(group):
                self.group[v] = group
            if group & heads:
                self.U |= group
            elif group.bit_count() == 1:
                self.singletons |= group
        self.S = self.full ^ self.U

    def y_space(self, equations, ymask):
        # All variables outside ymask are fixed to zero in this local solver.
        rows = equations + [(1 << v, 0) for v in bits(self.full ^ ymask)]
        return affine(rows, self.n)

    def single_rank(self, S, Y, base, equations):
        """Solve a branch with at most one nonzero readout row on S.

        base fixes all sites outside S|Y. Equations use original site indices.
        Removed ordinary pairs and released heads are reconstructed only at end.
        """
        beta = 0
        restrictions = []
        for row, rhs in equations:
            source = row & S
            yrow = row & Y
            rhs ^= parity(row & base)
            if not source:
                restrictions.append((yrow, rhs))
            elif not beta:
                beta, beta_y, beta_rhs = source, yrow, rhs
            else:
                assert source == beta
                restrictions.append((yrow ^ beta_y, rhs ^ beta_rhs))
        space = self.y_space(restrictions, Y)
        if space is None:
            return None
        origin, directions = space
        if not beta:
            return base ^ origin
        # On a solution with source parity zero the empty source suffices.
        if parity(origin & beta_y) == beta_rhs:
            return base ^ origin
        for direction in directions:
            if parity(direction & beta_y):
                return base ^ origin ^ direction
        ordinary = S & ~self.singletons
        if ordinary & beta:
            return base ^ origin ^ ((ordinary & beta) & -(ordinary & beta))
        tails = S & self.singletons
        # Failure is affine jointly in y and the unmarked ordinary helpers.
        trials = [0, *directions, *(1 << i for i in bits(ordinary))]
        for direction in trials:
            word = base ^ origin ^ direction
            slack = sum(1 << i for i in bits(tails)
                        if any((word >> h) & 1 == b for h, b in self.releases[i]))
            if beta & slack:
                return word | ((beta & slack) & -(beta & slack))
            guarded = tails & ~slack
            # Slack sites are unmarked. One of zero and the unit settings
            # escapes whenever their induced affine failure equations can fail.
            for helper in [0, *(1 << j for j in bits(slack))]:
                y = word | helper
                drift = self.offset ^ sum(parity(row & y) << i
                                          for i, row in enumerate(self.rows))
                selected = mixed(self.rows, guarded, drift, beta)
                if selected is not None:
                    return selected | y
        return None

    def free_pair(self, i, j):
        gi, gj = self.group[i], self.group[j]
        if gi == gj and gi.bit_count() == 2:
            return None
        literals = []
        for v in (i, j):
            literals.append(self.releases[v] if self.singletons >> v & 1 else [None])
        for li, lj in product(*literals):
            if li and lj and li[0] == lj[0] and li[1] != lj[1]:
                continue
            head = sum(1 << h for h, val in set(lit for lit in (li, lj) if lit) if val)
            shift = self.target
            for v in bits(head):
                shift ^= self.labels[v]
            for take_i, take_j in product(range(2), repeat=2):
                if (take_i*self.labels[i] ^ take_j*self.labels[j]) == shift:
                    return head | (take_i << i) | (take_j << j)
        return None

    def binary_pair(self, i, j):
        pair = (1 << i) | (1 << j)
        remain = self.S ^ pair
        for base in (0, 1 << i, 1 << j):
            word = self.single_rank(remain, self.U, base, self.readouts)
            if word is not None:
                return word
        K = {0}
        for a, b, table in self.ordinary:
            if ((1 << a) | (1 << b)) == pair:
                ds = [d if a == i else ((d & 1) << 1 | d >> 1)
                      for d in range(4) if table >> (12+d) & 1]
                K = {old ^ d for d in ds for old in K}
        for ri, rj in product([None, *self.releases[i]], [None, *self.releases[j]]):
            pins = [(1 << h, value) for h, value in (r for r in (ri, rj) if r)]
            for first, second in combinations(sorted(K), 2):
                delta = first ^ second
                normal = (delta >> 1) | ((delta & 1) << 1)
                row = 0
                rhs = parity(normal & first)
                for axis, v, release in ((1, i, ri), (2, j, rj)):
                    if normal & axis:
                        row ^= self.rows[v]
                        rhs ^= ((self.offset >> v) & 1) ^ int(release is not None)
                word = self.single_rank(remain, self.U, pair,
                                        self.readouts + pins + [(row, rhs)])
                if word is not None:
                    return word
        return None

    def occupancy(self):
        marked = [v for v in bits(self.S) if self.labels[v]]
        if len({self.labels[v] for v in marked}) <= 1:
            return self.single_rank(self.S, self.U, 0, self.readouts)
        independent = [(i, j) for i, j in combinations(marked, 2)
                       if self.labels[i] != self.labels[j]]
        for i, j in independent:
            word = self.free_pair(i, j)
            if word is not None:
                return word
        i, j = independent[0]
        if not (self.singletons >> i & 1):
            return self.binary_pair(i, j)
        head = self.releases[i][0][0]
        for value in (0, 1):
            released = sum(1 << v for v in marked if (head, value) in self.releases[v])
            word = self.single_rank(self.S ^ released, self.U | released, 0,
                                    self.readouts + [(1 << head, value)])
            if word is not None:
                return word
        return None


def solve(rows, c, edges, labels, target):
    """Return (occupancy, per-edge defects) or None on a valid input."""
    word = Network(rows, c, edges, labels, target).occupancy()
    if word is None:
        return None
    defects = fixed(rows, c, edges, word)
    observed = 0
    for v in bits(word):
        observed ^= labels[v]
    assert observed == target and defects is not None
    assert verify(rows, c, edges, word, defects)
    return word, defects

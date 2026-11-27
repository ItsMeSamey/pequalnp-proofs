"""Online exact counts for Boolean flat indicators selecting quadratic probes.

A flat is a tuple of (mask, bit) equations over the h seed coordinates.
SelectedQuery.specialize receives the tuple of membership bits in supplied order.
It must be deterministic and must return a Quadratic.
"""
from dataclasses import dataclass
from typing import Callable

from quadratic_polar_online import (
    Quadratic, _bit, _dot, _nonnegative, _pull, _space, _validate_query,
    count_histogram,
)


@dataclass(frozen=True)
class SelectedQuery:
    flats: tuple
    specialize: Callable[[tuple], Quadratic]

    def __post_init__(self):
        object.__setattr__(self, "flats", tuple(tuple(tuple(eq) for eq in f) for f in self.flats))


def _flat(h, equations):
    """Canonical reduced affine equation basis, or None for the empty set."""
    pivots = {}
    for mask, bit in equations:
        if _nonnegative(mask).bit_length() > h:
            raise ValueError("out-of-range flat coordinate")
        bit = _bit(bit)
        for j in sorted(pivots, reverse=True):
            if (mask >> j) & 1:
                row, rhs = pivots[j]
                mask ^= row
                bit ^= rhs
        if not mask:
            if bit:
                return None
            continue
        j = mask.bit_length() - 1
        for i, (row, rhs) in tuple(pivots.items()):
            if (row >> j) & 1:
                pivots[i] = row ^ mask, rhs ^ bit
        pivots[j] = mask, bit
    return tuple(pivots[j] for j in sorted(pivots))


def _inside(h, small, large):
    return large is not None and _flat(h, (*small, *large)) == small


class _BudgetFailure(Exception):
    pass


class _Arrangement:
    def __init__(self, h, flats, max_intersections):
        nodes = {()}
        for flat in flats:
            if flat is None:
                continue
            for node in tuple(nodes):
                intersection = _flat(h, (*node, *flat))
                if intersection is not None:
                    nodes.add(intersection)
                    if max_intersections is not None and len(nodes) > max_intersections:
                        raise _BudgetFailure
        # Strict subflats always precede their supersets.
        self.nodes = sorted(nodes, key=lambda node: (-len(node), node))
        self.below = {}
        self.patterns = {}
        self.atom_sizes = {}
        for i, node in enumerate(self.nodes):
            self.below[node] = [other for other in self.nodes[:i] if _inside(h, other, node)]
            self.atom_sizes[node] = (1 << (h - len(node))) - sum(
                self.atom_sizes[other] for other in self.below[node])
            self.patterns[node] = tuple(_inside(h, node, f) for f in flats)


class _Round:
    def __init__(self, learner, query):
        self.learner = learner
        self.query = query
        h = learner.h
        self.flats = learner.flats + query.flats
        self.arr = _Arrangement(h, [_flat(h, f) for f in self.flats], learner.max_intersections)
        self.systems = {}
        for node in self.arr.nodes:
            if not self.arr.atom_sizes[node]:
                continue
            pattern = self.arr.patterns[node]
            old = learner.hulls.get(pattern[:len(learner.flats)])
            if old is None:
                continue
            system = []
            offset = 0
            for past, label in (*learner.history, (query, None)):
                end = offset + len(past.flats)
                quadratic = past.specialize(pattern[offset:end])
                _validate_query(h, quadratic)
                system.append((quadratic, label))
                offset = end
            self.systems[node] = old, system

    def count(self, node, pins=()):
        """Count the exact atom using one frozen polynomial system throughout."""
        if node not in self.systems:
            return (0, 0)
        learner = self.learner
        hull, system = self.systems[node]
        exact = {}
        for sub in [*self.arr.below[node], node]:
            space = _space(learner.h, (*hull, *sub, *pins))
            totals = (0, 0)
            if space is not None:
                origin, directions, _ = space
                pulled = [(_pull(q, learner.h, origin, directions), label) for q, label in system]
                totals = count_histogram(len(directions), learner.k, learner.r,
                                         pulled[:-1], pulled[-1][0])
                if totals is None:
                    raise _BudgetFailure
            n0, n1 = totals
            for proper in self.arr.below[sub]:
                a, b = exact[proper]
                n0 -= a
                n1 -= b
            exact[sub] = n0, n1
        return exact[node]

    def hull(self, node, label):
        """Grow the affine span of witnesses located by constrained counts."""
        h = self.learner.h

        def witness(pins):
            point = 0
            for j in range(h):
                row = 1 << j
                bit = int(not self.count(node, (*pins, (row, 0)))[label])
                pins = (*pins, (row, bit))
                point |= bit << j
            return point

        origin = witness(())
        directions = []
        while True:
            _, normals, _ = _space(h, ((v, 0) for v in directions))
            equations = [(a, _dot(a, origin)) for a in normals]
            for a, b in equations:
                outside = ((a, 1 ^ b),)
                if self.count(node, outside)[label]:
                    directions.append(witness(outside) ^ origin)
                    break
            else:
                return _flat(h, equations)


class FlatLearner:
    def __init__(self, h, k, r, max_intersections=None):
        self.h, self.k, self.r = map(_nonnegative, (h, k, r))
        if max_intersections is not None and _nonnegative(max_intersections) < 1:
            raise ValueError("max_intersections must allow the ambient flat")
        self.max_intersections = max_intersections
        self.history = ()
        self.flats = ()
        self.hulls = {(): ()}

    def _prepare(self, query):
        round_ = _Round(self, query)
        counts = {node: round_.count(node) for node in round_.arr.nodes}
        totals = tuple(sum(pair[b] for pair in counts.values()) for b in (0, 1))
        return round_, counts, totals

    def histogram(self, query):
        try:
            return self._prepare(query)[2]
        except _BudgetFailure:
            return None

    def predict(self, query):
        counts = self.histogram(query)
        return int(counts is not None and counts[1] > counts[0])

    def observe(self, query, label):
        """Commit an erroneous observation atomically; ties predict zero."""
        label = _bit(label)
        try:
            round_, counts, totals = self._prepare(query)
        except _BudgetFailure as exc:
            raise ValueError("query exceeds discovery budget") from exc
        if not totals[label]:
            raise ValueError("label inconsistent with the maintained version space")
        if int(totals[1] > totals[0]) == label:
            return False
        hulls = {round_.arr.patterns[node]: round_.hull(node, label)
                 for node, pair in counts.items() if pair[label]}
        self.hulls = hulls
        self.history += ((query, label),)
        self.flats = round_.flats
        return True

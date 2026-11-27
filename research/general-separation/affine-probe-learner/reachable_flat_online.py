"""Exact majority prediction for sparse reachable flat signatures.

SelectedQuery and Quadratic use the representations in flat_selected_online.
max_signatures bounds positive signatures per frozen old hull at every prefix,
including signatures inconsistent with that hull's historical membership mask.
max_cells optionally bounds total retained (historically matching) signatures
in the current provisional refinement. Budget failure leaves state unchanged.
"""
from flat_selected_online import (
    FlatLearner, SelectedQuery, _BudgetFailure, _Round, _flat,
)
from quadratic_polar_online import Quadratic, _bit, _nonnegative, _pull, _space, count_histogram


_ZERO = Quadratic(0, 0, 0)


class _Local:
    def __init__(self, learner, hull, stored, flats):
        self.learner = learner
        self.hull = hull
        self.stored = stored
        self.flats = flats

    def positive(self, mask, current, pins=()):
        equations = [*self.hull, *pins]
        while mask:
            bit = mask & -mask
            flat = self.flats[bit.bit_length() - 1]
            if flat is None:
                return (0, 0)
            equations.extend(flat)
            mask ^= bit
        learner = self.learner
        space = _space(learner.h, equations)
        if space is None:
            return (0, 0)
        origin, directions, _ = space
        def pull(row):
            return _pull(row, learner.h, origin, directions)
        result = count_histogram(len(directions), learner.k, learner.r,
                                 [(pull(q), b) for q, b in self.stored], pull(current))
        if result is None:
            raise _BudgetFailure
        return result

    def discover(self):
        counts = {0: sum(self.positive(0, _ZERO))}
        if not counts[0]:
            return {}
        for index in range(len(self.flats)):
            bit = 1 << index
            hit = {}
            refined = {}
            for mask in sorted(counts, key=int.bit_count, reverse=True):
                total = sum(self.positive(mask | bit, _ZERO))
                exact = total - sum(v for other, v in hit.items() if other & mask == mask)
                hit[mask] = exact
                if exact:
                    refined[mask | bit] = exact
                if counts[mask] > exact:
                    refined[mask] = counts[mask] - exact
                if len(refined) > self.learner.max_signatures:
                    raise _BudgetFailure
            counts = refined
        return counts


class _ReachableRound(_Round):
    # Inherit the witness-by-pinning affine hull algorithm, calling our count.
    def __init__(self, learner, query):
        self.learner = learner
        self.flats = learner.flats + query.flats
        canonical = tuple(_flat(learner.h, f) for f in self.flats)
        self.cells = {}
        old_width = len(learner.flats)
        for old_pattern, hull in learner.hulls.items():
            stored = []
            start = 0
            for past, label in learner.history:
                end = start + len(past.flats)
                stored.append((past.specialize(old_pattern[start:end]), label))
                start = end
            local = _Local(learner, hull, stored, canonical)
            support = sorted(local.discover(), key=int.bit_count, reverse=True)
            for mask in support:
                pattern = tuple(bool(mask & (1 << i)) for i in range(len(canonical)))
                if pattern[:old_width] != old_pattern:
                    continue
                current = query.specialize(pattern[old_width:])
                supersets = [other for other in support if other & mask == mask]
                self.cells[pattern] = local, supersets, mask, current
                if learner.max_cells is not None and len(self.cells) > learner.max_cells:
                    raise _BudgetFailure

    def count(self, node, pins=()):
        local, supersets, mask, current = self.cells[node]
        exact = {}
        for other in supersets:
            a, b = local.positive(other, current, pins)
            for above, (x, y) in exact.items():
                if above & other == other:
                    a -= x
                    b -= y
            exact[other] = a, b
        return exact[mask]


class ReachableFlatLearner(FlatLearner):
    """Store actual feasible hulls on mistakes; ties predict zero.

    For P prefix tests, L old hulls and local cap S, discovery uses at most
    L(1+P*S) positive histogram calls and O(L*P*S**2) comparisons.
    For C kept cells each histogram uses at most C*S positive calls; a
    mistaken-label hull reconstruction multiplies that by O((h+1)**2).
    Each positive call intersects at most P flats plus its hull and pins and
    invokes the quadratic polar counter at most once. Mask work is polynomial
    in P. Callable selectors are deterministic and must return valid rows.
    """
    def __init__(self, h, k, r, max_signatures, max_cells=None):
        super().__init__(h, k, r)
        self.max_signatures = _nonnegative(max_signatures)
        if not self.max_signatures:
            raise ValueError("max_signatures must be positive")
        self.max_cells = None if max_cells is None else _nonnegative(max_cells)

    def _prepare(self, query):
        round_ = _ReachableRound(self, query)
        counts = {node: round_.count(node) for node in round_.cells}
        totals = tuple(sum(pair[b] for pair in counts.values()) for b in (0, 1))
        return round_, counts, totals

    def observe(self, query, label):
        label = _bit(label)
        try:
            round_, counts, totals = self._prepare(query)
            if not totals[label]:
                raise ValueError("label inconsistent with maintained version space")
            if int(totals[1] > totals[0]) == label:
                return False
            hulls = {node: round_.hull(node, label)
                     for node, pair in counts.items() if pair[label]}
        except _BudgetFailure as exc:
            raise ValueError("query exceeds discovery budget") from exc
        self.hulls = hulls
        self.history += ((query, label),)
        self.flats = round_.flats
        return True

"""Online prediction of Boolean readouts of binary affine measurements.

AffineProbeLearner.predict issues a prediction, then update accepts its label.
All mask coordinates use least significant bit first.
"""
from collections.abc import Callable, Iterable, Sequence
from dataclasses import dataclass


def _bit(value: int) -> int:
    if not isinstance(value, int) or value not in (0, 1):
        raise ValueError("expected a Boolean bit")
    return int(value)


def _mask(value: int, width: int) -> int:
    if not isinstance(value, int) or value < 0 or value.bit_length() > width:
        raise ValueError(f"expected a nonnegative mask of width {width}")
    return int(value)


def _dot(left: int, right: int) -> int:
    return (left & right).bit_count() & 1


def _extend(basis: tuple[int, ...], vector: int) -> tuple[int, ...]:
    """Insert into a descending-pivot echelon basis."""
    for row in basis:
        if vector & (1 << (row.bit_length() - 1)):
            vector ^= row
    if not vector:
        return basis
    return tuple(sorted((*basis, vector), reverse=True))


@dataclass(frozen=True)
class _Cell:
    origin: int
    directions: tuple[int, ...]

    def restrict(self, row: int, bit: int):
        """Intersect with row dot seed = bit. None denotes an empty cell."""
        mismatch = _dot(self.origin, row) ^ bit
        pivot = next((d for d in self.directions if _dot(d, row)), None)
        if pivot is None:
            return None if mismatch else self
        origin = self.origin ^ pivot if mismatch else self.origin
        directions = tuple(d ^ pivot if _dot(d, row) else d
                           for d in self.directions if d != pivot)
        return _Cell(origin, directions)


@dataclass(frozen=True)
class _Expert:
    basis: tuple[int, ...]
    cell: _Cell


def _split_forms(basis: tuple[int, ...], rows: tuple[int, ...]) -> list[int]:
    """Three original rows independent modulo W, or fewer if resolved."""
    selected = []
    for row in rows:
        extended = _extend(basis, row)
        if len(extended) != len(basis):
            basis = extended
            selected.append(row)
            if len(selected) == 3:
                break
    return selected


def _measure(rows: tuple[int, ...], vector: int) -> int:
    return sum(_dot(row, vector) << i for i, row in enumerate(rows))


def _vote(cell: _Cell, rows: tuple[int, ...], offset: int,
          evaluate: Callable[[int], int]) -> tuple[int, _Cell | None]:
    """Return the vote and the inverse image of the opposite bit."""
    base = offset ^ _measure(rows, cell.origin)
    image_basis = ()
    for direction in cell.directions:
        image_basis = _extend(image_basis, _measure(rows, direction))
    if len(image_basis) > 2:
        raise AssertionError("unresolved measurement image")
    points = [base]
    for delta in image_basis:
        points += [point ^ delta for point in points]
    values = [_bit(evaluate(point)) for point in points]
    vote = int(2 * sum(values) > len(values))
    opposite = [point for point, bit in zip(points, values) if bit != vote]
    if not opposite:
        return vote, None

    # These output coordinates distinguish every point of the affine image.
    coordinates = [delta.bit_length() - 1 for delta in image_basis]

    def fiber(point: int) -> _Cell:
        result = cell
        for i in coordinates:
            result = result.restrict(rows[i], ((point ^ offset) >> i) & 1)
            if result is None:
                raise AssertionError("image point has empty fiber")
        return result

    first = fiber(opposite[0])
    if len(opposite) == 1:
        return vote, first
    # Two parallel fibers over F2 have affine union; their offset difference
    # is independent of the common kernel.
    second = fiber(opposite[1])
    return vote, _Cell(first.origin,
                       (*first.directions, first.origin ^ second.origin))


class AffineProbeLearner:
    """Learn from repeated probes of a fixed h-bit hidden seed.

    predict(row_masks, offset, readout) issues a bit. Measurement j is
    parity(row_masks[j] & seed) XOR bit j of offset. A total callable receives
    the packed integer of those measurements. A truth table is a sequence of
    2**len(row_masks) bits indexed by that same integer. Only the entries
    actually evaluated are inspected. update(label) ends the pending round and
    returns True exactly on a mistake. Correct rounds retain the committed state.

    Ties and empty votes predict zero. If a single subspace W of dimension at
    most k leaves at most two independent measurements modulo W on every
    mistaken round, mistakes <= (h*ln(2)+k*ln(7))/ln(4/3). The protocol is
    also defined when the promise fails.
    """

    def __init__(self, h: int, k: int):
        if not all(isinstance(n, int) and n >= 0 for n in (h, k)):
            raise ValueError("h and k must be nonnegative integers")
        self._h = h
        self._k = k
        self._scale = 7 ** k
        self._mistakes = 0
        cube = _Cell(0, tuple(1 << i for i in range(h)))
        self._experts = [_Expert((), cube)]
        self._pending = None

    @property
    def mistakes(self) -> int:
        return self._mistakes

    @property
    def expert_count(self) -> int:
        return len(self._experts)

    @property
    def mass_denominator(self) -> int:
        return self._scale

    def _mass(self, expert: _Expert) -> int:
        return (7 ** (self._k - len(expert.basis))) << len(expert.cell.directions)

    @property
    def mass_numerator(self) -> int:
        return sum(self._mass(expert) for expert in self._experts)

    def committed_cells(self) -> tuple:
        """Immutable (W basis, seed origin, seed directions) triples, with multiplicity."""
        return tuple((e.basis, e.cell.origin, e.cell.directions) for e in self._experts)

    def predict(self, row_masks: Iterable[int], offset: int,
                readout: Sequence[int] | Callable[[int], int]) -> int:
        if self._pending is not None:
            raise RuntimeError("call update before another prediction")
        rows = tuple(_mask(row, self._h) for row in row_masks)
        offset = _mask(offset, len(rows))
        if callable(readout):
            evaluate = readout
        else:
            if not isinstance(readout, Sequence):
                raise TypeError("readout must be a truth table or a callable")
            if len(readout) != 1 << len(rows):
                raise ValueError("truth table length does not match measurement count")
            evaluate = readout.__getitem__

        stack = list(self._experts)
        resolved = []
        mass = [0, 0]
        while stack:
            expert = stack.pop()
            forms = _split_forms(expert.basis, rows)
            if len(forms) < 3:
                bit, opposite = _vote(expert.cell, rows, offset, evaluate)
                mass[bit] += self._mass(expert)
                resolved.append((expert, bit, opposite))
                continue
            if len(expert.basis) == self._k:
                continue
            a, b, c = forms
            for row in (a, b, c, a ^ b, a ^ c, b ^ c, a ^ b ^ c):
                extended = _extend(expert.basis, row)
                for value in (0, 1):
                    child = expert.cell.restrict(row, value)
                    if child is not None:
                        stack.append(_Expert(extended, child))
        prediction = int(mass[1] > mass[0])
        self._pending = prediction, resolved
        return prediction

    def update(self, label: int) -> bool:
        if self._pending is None:
            raise RuntimeError("call predict before supplying a label")
        label = _bit(label)
        prediction, resolved = self._pending
        if label != prediction:
            survivors = []
            for expert, bit, opposite in resolved:
                if bit == label:
                    survivors.append(expert)
                elif opposite is not None:
                    survivors.append(_Expert(expert.basis, opposite))
            self._experts = survivors
            self._mistakes += 1
        self._pending = None
        return label != prediction

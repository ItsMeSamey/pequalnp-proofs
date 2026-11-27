"""Correct one external baseline count using sparse original-label replacements.

IDs are q-bit integers. decode(id) returns None for an inactive slot or three
(label,negated) pairs. Negated 0 means positive; a literal is true iff
old_bit(label) XOR negated is one. incident(label) lists all active original
IDs containing the label, on ANY of the three positions. Distinct IDs encoding
the same clause are distinct baseline contributions. Repeated emissions are
allowed and charged. All callbacks must be deterministic.

The trusted baseline counts active false clauses on the entire ID domain under
old_bit, once per ID (unique extensions if computed with a gate CNF). Completeness
of incident() and correctness of the baseline cannot be inferred locally.
Returned counts concern precisely the same IDs and labels. A zero violation
count certifies the total witness obtained by overriding old_bit on the supplied
replacement labels, under these promises. No scratch label enters that witness.

For t patches and E raw emissions, use O(t+E) records and O((t+E+1)
log(t+E+2)) comparisons, in addition to t enumerator calls, at most E
decoder calls, and at most 3E old-bit calls. Charge identifier bit lengths and
callback costs separately. The single external baseline computation is an
additive cost, even when E=0. Sorts below use Python's built-in in-memory sort.
"""
from dataclasses import dataclass
from itertools import islice


@dataclass(frozen=True)
class Correction:
    violations: int
    old_affected: int
    new_affected: int
    affected_ids: int
    emissions: int


def _natural(value, name):
    if type(value) is not int or value < 0:
        raise ValueError(f"invalid {name}")
    return value


def _word(value, width, name):
    if _natural(value, name).bit_length() > width:
        raise ValueError(f"out-of-range {name}")
    return value


def _bit(value):
    if type(value) not in (bool, int) or value not in (0, 1):
        raise ValueError("expected a bit")
    return int(value)


def correct_violations(q, label_bits, decode, incident, old_bit, replacements,
                       baseline, *, max_emissions_per_label):
    """Return exact corrected ID count. Reject detectable interface violations."""
    _natural(q, "ID width")
    _natural(label_bits, "label width")
    _natural(max_emissions_per_label, "occurrence cap")
    if _natural(baseline, "baseline") > 1 << q:
        raise ValueError("baseline exceeds ID domain")

    patches = []
    previous = -1
    emitted = []
    for label, bit in replacements:
        _word(label, label_bits, "patch label")
        if label <= previous:
            raise ValueError("replacement labels must be strictly increasing")
        previous = label
        patches.append((label, _bit(bit)))
        for index, clause_id in enumerate(incident(label)):
            if index >= max_emissions_per_label:
                raise ValueError("occurrence cap exceeded")
            emitted.append((_word(clause_id, q, "clause ID"), label))

    emitted.sort()
    positions = []
    affected = 0
    cursor = 0
    while cursor < len(emitted):
        clause_id = emitted[cursor][0]
        clause = decode(clause_id)
        if clause is None:
            raise ValueError("generator emitted an inactive ID")
        # Read at most four items, including on an invalid infinite generator.
        clause = tuple(islice(clause, 4))
        if len(clause) != 3:
            raise ValueError("active clause must have exactly three positions")
        labels = []
        for pos, (label, sign) in enumerate(clause):
            labels.append(_word(label, label_bits, "decoded label"))
            positions.append((label, clause_id, pos, _bit(sign)))
        while cursor < len(emitted) and emitted[cursor][0] == clause_id:
            if emitted[cursor][1] not in labels:
                raise ValueError("generator emitted a clause without its label")
            cursor += 1
        affected += 1

    positions.sort()
    values = []
    cursor = 0
    for label, clause_id, pos, sign in positions:
        while cursor < len(patches) and patches[cursor][0] < label:
            cursor += 1
        old = _bit(old_bit(label))
        new = patches[cursor][1] if cursor < len(patches) and patches[cursor][0] == label else old
        values.append((clause_id, pos, old ^ sign, new ^ sign))
    values.sort()
    old_false = new_false = 0
    for i in range(0, len(values), 3):
        triple = values[i:i+3]
        old_false += not any(row[2] for row in triple)
        new_false += not any(row[3] for row in triple)

    outside = baseline-old_false
    if not 0 <= outside <= (1 << q)-affected:
        raise ValueError("baseline inconsistent with observed affected IDs")
    return Correction(outside+new_false, old_false, new_false, affected, len(emitted))

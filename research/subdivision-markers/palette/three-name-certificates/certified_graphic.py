"""Verified graphicness using the sibling three-name-backend on PYTHONPATH."""
from dataclasses import dataclass
from functools import partial
from graphic import is_graphic_cmr
from minor_check import match_excluded_minor, verify_minor


@dataclass(frozen=True)
class Obstruction:
    target: str
    retain: tuple
    contract: tuple
    delete: tuple


def contracted(columns, position):
    vector = columns[position]
    pivot = 1 << (vector.bit_length() - 1) if vector else 0
    return tuple(v ^ vector if v & pivot else v
                 for j, v in enumerate(columns) if j != position)


def find_obstruction(original, decide):
    """Untrusted decision hints guide descent. Verify the final original-index minor."""
    current = tuple(original)
    ids = list(range(len(current)))
    contract_ids = []
    delete_ids = []
    for label in range(len(current)):
        i = ids.index(label)
        deleted = current[:i] + current[i + 1:]
        if not decide(deleted):
            delete_ids.append(ids.pop(i))
            current = deleted
            continue
        quotient = contracted(current, i)
        if not decide(quotient):
            contract_ids.append(ids.pop(i))
            current = quotient
    # A skipped label had graphic deletion and contraction. All subsequent
    # operations are on other labels and preserve graphicness of those minors.
    match = match_excluded_minor(current)
    if match is None:
        raise ValueError("unable to verify a nongraphic obstruction")
    target, indices = match
    retained = tuple(ids[i] for i in indices)
    if not verify_minor(original, retained, contract_ids, delete_ids, target):
        raise ValueError("excluded minor failed independent verification")
    return Obstruction(target, retained, tuple(contract_ids), tuple(delete_ids))


def graphic_or_obstruction(columns, *, executable="cmr-graphic", timeout=30, memory_mib=256):
    """Return None on verified graphicness, otherwise a verified excluded minor."""
    original = tuple(columns)
    decide = partial(is_graphic_cmr, executable=executable, timeout=timeout, memory_mib=memory_mib)
    if decide(original):
        return None
    return find_obstruction(original, decide)


def is_graphic_certified(columns, **options):
    return graphic_or_obstruction(columns, **options) is None

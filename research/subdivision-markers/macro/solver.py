"""Exact witnesses for layered affine-guarded blocks.

layers[layer][block] lists (global_output_mask, literals). Zero is always an
additional choice. A literal (mask, constant) is true iff parity(mask & state)
XOR constant equals one. A marker (mask, rhs) requires parity to equal rhs.
solve returns (global_state, layers_of_option_indices); -1 means baseline.
"""
from itertools import combinations, product
from math import prod
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from prg.viola import block as selector_bits, field_modulus


def parity(mask):
    return mask.bit_count() & 1


def normalized(rows):
    basis = {}
    for mask, rhs in rows:
        while mask:
            p = mask.bit_length() - 1
            if p not in basis:
                basis[p] = mask, rhs
                break
            v, c = basis[p]
            mask ^= v
            rhs ^= c
        if not mask and rhs:
            return None
    return tuple(basis.values())


def projected(clauses, force_dense=False):
    """Yield tuples of equations whose solution sets cover the clause solutions."""
    if not clauses:
        yield ()
        return
    if not all(clauses):
        return
    total = sum(map(len, clauses))
    degree = (total - 1).bit_length() + len(clauses) + 1
    q = 1 << degree
    if not force_dense and prod(map(len, clauses)) <= q*q:
        for chosen in product(*clauses):
            yield tuple((mask, 1 ^ c) for mask, c in chosen)
        return
    modulus = field_modulus(degree)
    for alpha in range(q):
        for gamma in range(q):
            s = selector_bits(total, alpha, gamma, modulus)
            rows = []
            for clause in clauses:
                mask, rhs = 0, 1
                for m, c in clause:
                    if s & 1:
                        mask ^= m
                        rhs ^= c
                    s >>= 1
                rows.append((mask, rhs))
            yield tuple(rows)


def signature(i, positions):
    return sum(((i >> p) & 1) << j for j, p in enumerate(positions))


def solve(layers, markers):
    all_support = 0
    supports = []
    for layer in layers:
        support = 0
        for options in layer:
            owned = 0
            for v, literals in options:
                if v < 0 or any(m < 0 or c not in (0, 1) for m, c in literals):
                    raise ValueError("invalid option")
                owned |= v
            if owned & (support | all_support):
                raise ValueError("overlapping block supports")
            support |= owned
        supports.append(support)
        all_support |= support
    earlier = 0
    for layer, support in zip(layers, supports):
        for options in layer:
            for _, literals in options:
                if any(m & all_support & ~earlier for m, _ in literals):
                    raise ValueError("guard depends on a current or later block")
        earlier |= support
    if any(mask < 0 or rhs not in (0, 1) for mask, rhs in markers):
        raise ValueError("invalid marker")

    def search(d, rows):
        rows = normalized(rows)
        if rows is None:
            return None
        if not d:
            return None if any(rhs for _, rhs in rows) else (0, [])
        layer = layers[d - 1]
        restricted = tuple((m & ~supports[d - 1], rhs) for m, rhs in rows)
        baseline = search(d - 1, restricted)
        if baseline is not None:
            state, choices = baseline
            return state, choices + [[-1] * len(layer)]
        entries = []
        for i, options in enumerate(layer):
            for j, (out, literals) in enumerate(options):
                delta = sum(parity(out & mask) << t for t, (mask, _) in enumerate(rows))
                if delta and literals:
                    entries.append((i, j, delta, literals))
        width = (max(len(layer), 1) - 1).bit_length()
        max_choices = min(len(rows), len({i for i, *_ in entries}))
        for size in range(1, max_choices + 1):
            # Any distinguishing subset can be padded to this many positions.
            for positions in combinations(range(width), min(size - 1, width)):
                buckets = {}
                for i, j, delta, lits in entries:
                    sig = signature(i, positions)
                    buckets.setdefault(sig, {}).setdefault(delta, []).append((i, j, lits))
                for ids in combinations(sorted(buckets), size):
                    for deltas in product(*(buckets[s] for s in ids)):
                        correction = 0
                        clauses = []
                        candidates = []
                        for s, delta in zip(ids, deltas):
                            correction ^= delta
                            options = buckets[s][delta]
                            candidates.append(options)
                            clauses.append(tuple(dict.fromkeys(lit for _, _, ls in options for lit in ls)))
                        adjusted = tuple((m, rhs ^ (correction >> t & 1))
                                         for t, (m, rhs) in enumerate(restricted))
                        for extra in projected(clauses):
                            prefix = search(d - 1, adjusted + extra)
                            if prefix is None:
                                continue
                            state, choices = prefix
                            current = [-1] * len(layer)
                            added = 0
                            for options in candidates:
                                i, j = next((i, j) for i, j, ls in options
                                            if any(parity(state & m) ^ c for m, c in ls))
                                current[i] = j
                                added |= layer[i][j][0]
                            return state | added, choices + [current]
        return None

    return search(len(layers), markers)

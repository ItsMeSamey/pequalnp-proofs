"""Enumerate separating one-donor substitutions for minimum original banks."""

from itertools import combinations


def generate_banks(old, paid, features, positive, negative):
    """Return (sorted banks, provenance) using bit i of each feature for cell i.

    The provenance dict contains mandatory wire IDs, minimum optional subsets,
    and their corresponding complete minimum banks, all in sorted order.
    """
    old = tuple(sorted(set(old)))
    paid = tuple(sorted(set(paid)))
    index = {wire: 1 << i for i, wire in enumerate(paid)}
    all_bits = (1 << len(paid)) - 1

    def bank_mask(wires):
        return sum(index[wire] for wire in wires)

    def signatures(cells):
        return {sum(index[w] for w in paid if features[w] >> cell & 1)
                for cell in cells}

    pos = signatures(positive)
    neg = signatures(negative)
    original_mask = bank_mask(old)
    original_pos = {p & original_mask for p in pos}
    original_neg = {n & original_mask for n in neg}
    if original_pos & original_neg:
        raise ValueError("Original bank fails to separate the specified cells")

    mandatory = tuple(w for w in old if any((p ^ index[w]) in original_neg
                                             for p in original_pos))
    required = bank_mask(mandatory)
    optional = sorted(set(old) - set(mandatory))
    minimum_options = []
    for size in range(len(optional) + 1):
        for choice in combinations(optional, size):
            mask = required | bank_mask(choice)
            if {p & mask for p in original_pos}.isdisjoint(n & mask for n in original_neg):
                minimum_options.append(choice)
        if minimum_options:
            break

    def constant_bits(signatures_, mask):
        groups = {}
        for value in signatures_:
            key = value & mask
            ones, zeros = groups.get(key, (all_bits, all_bits))
            groups[key] = (ones & value, zeros & ~value)
        return groups

    minimum_banks = sorted(tuple(sorted(mandatory + choice)) for choice in minimum_options)
    banks = set()
    for bank in minimum_banks:
        mask = bank_mask(bank)
        positives = constant_bits(pos, mask)
        negatives = constant_bits(neg, mask)
        unused = all_bits ^ mask

        def viable(difference):
            donors = unused
            for key, (ones, zeros) in positives.items():
                opposing = negatives.get(key ^ difference)
                if opposing is not None:
                    n_ones, n_zeros = opposing
                    donors &= (ones & n_zeros) | (zeros & n_ones)
                    if not donors:
                        break
            return donors

        singles = {w: viable(index[w]) for w in bank}
        for left, right in combinations(bank, 2):
            donors = singles[left] & singles[right]
            if donors:
                donors &= viable(index[left] | index[right])
            while donors:
                bit = donors & -donors
                donor = paid[bit.bit_length() - 1]
                banks.add(tuple(sorted((set(bank) - {left, right}) | {donor})))
                donors ^= bit

    return sorted(banks), dict(mandatory=mandatory, minimum_options=minimum_options,
                               minimum_banks=minimum_banks)

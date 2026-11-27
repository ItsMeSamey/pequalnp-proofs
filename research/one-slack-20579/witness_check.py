"""Validate the singleton and triangle certificates on promised cells."""


def check_witnesses(witness, cases, bank, roots):
    """Raise ValueError if the certificate does not follow from the supplied cases."""
    def require(condition, message):
        if not condition:
            raise ValueError(message)

    def integer(value):
        return type(value) is int

    def mask(value):
        return integer(value) and 0 <= value < 1 << 15

    def check_cell(coords, claimed_mask, target):
        require(isinstance(coords, list) and len(coords) == 2
                and all(integer(x) and 0 <= x < 32 for x in coords),
                f"invalid coordinates {coords!r}")
        cell = tuple(coords)
        require(cell in cases, f"missing case {cell}")
        bits, label, outside = cases[cell]
        require(mask(claimed_mask) and mask(bits) and bits == claimed_mask
                and label == target and outside == 0, f"case mismatch at {cell}")
        return bits

    bank = list(bank)
    roots = list(roots)
    require(len(bank) == 15 and len(set(bank)) == 15, "expected 15 distinct bank wires")
    require(witness["bank"] == bank and all(integer(x) for x in witness["bank"]),
            "bank mismatch")
    require(witness["outputs"] == roots and all(integer(x) for x in witness["outputs"]),
            "output mismatch")
    oriented = witness["oriented"]
    require(set(oriented) == {str(w) for w in bank}, "incomplete singleton witnesses")
    for i, wire in enumerate(bank):
        record = oriented[str(wire)]
        pos = check_cell(record["positive"], record["positive_bits"], 1)
        neg = check_cell(record["negative"], record["negative_bits"], 0)
        require(pos ^ neg == 1 << i and pos & (1 << i), f"invalid singleton {wire}")

    expected = {(65, 102), (65, 107), (102, 107)}
    records = witness["triangle"]
    require(isinstance(records, list) and len(records) == 3, "expected three triangle edges")
    for edge in records:
        pair = tuple(edge["pair"])
        require(all(integer(x) for x in pair) and pair in expected, f"invalid edge {pair}")
        expected.remove(pair)
        a, b = (1 << bank.index(w) for w in pair)
        for field, patterns, labels in (
            ("or_corners", (0, a, b), (0, 1, 1)),
            ("and_corners", (a, b, a | b), (0, 0, 1)),
        ):
            corners = edge[field]
            require(isinstance(corners, list) and len(corners) == 3,
                    f"expected three {field} for {pair}")
            base = None
            for record, pattern, label in zip(corners, patterns, labels):
                corner = record["corner"]
                require(mask(corner) and integer(record["value"]) and record["value"] == label,
                        f"invalid corner or value for {pair}")
                original = check_cell(record["cell"], record["original_mask"], label)
                require((original & corner) == (original if label else corner),
                        f"invalid monotonicity direction for {pair}")
                if base is None:
                    base = corner & ~(a | b)
                require(corner == base | pattern, f"corner mismatch for {pair}")

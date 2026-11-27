"""Iterate distinct submasks in descending order, with optional zero."""
def submasks(mask: int, *, include_zero: bool = True):
    if mask < 0:
        raise ValueError("A mask must be nonnegative")
    current = mask
    while current:
        yield current
        current = (current - 1) & mask
    if include_zero:
        yield 0

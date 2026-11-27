"""All singleton traces attainable with free intersections and at most three unions."""
from itertools import combinations

left, right = 7, 25
free = {m for m in range(32) if (m & left).bit_count() <= 1 and (m & right).bit_count() <= 1}

def close(masks):
    while True:
        expanded = masks | {a & b for a, b in combinations(masks, 2)}
        if masks == expanded:
            return frozenset(masks)
        masks = expanded

states = {close(free)}
for depth, expected in enumerate([1, 15, 136, 887]):
    assert len(states) == expected
    assert all(not {left, right} <= state for state in states)
    print(depth, len(states), 'unreachable')
    if depth < 3:
        states = {close(state | {a | b})
                  for state in states for a, b in combinations(state, 2)
                  if a | b not in state}

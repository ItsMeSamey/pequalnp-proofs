"""Compare complete mask sets independently of the decrement/and recurrence."""
from itertools import combinations
from h5_submasks import submasks

def by_positions(mask):
    bits = [1 << i for i in range(mask.bit_length()) if mask >> i & 1]
    return {sum(group) for width in range(len(bits)+1) for group in combinations(bits,width)}

for mask in [*range(1024), 0xE421, 0xDB6D, 0xFFFF, (1<<79)|513]:
    expected = by_positions(mask)
    for include_zero in (True,False):
        values = list(submasks(mask,include_zero=include_zero))
        assert values == sorted(expected if include_zero else expected-{0},reverse=True)
try:
    list(submasks(-1))
except ValueError:
    pass
else:
    raise AssertionError("negative mask accepted")
print("1024 ten-bit masks plus four wide masks, both zero conventions passed")

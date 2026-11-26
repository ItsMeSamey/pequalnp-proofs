"""Exhaustively count selector extensions, including unused digit tuples."""
from itertools import product

for width in range(1, 9):
    for digits in range(1, 4):
        base = 1
        while base**digits < width:
            base += 1
        rows = []
        for indicators in product(range(2), repeat=base):
            if any(a and b for i,a in enumerate(indicators) for b in indicators[:i]):
                continue
            acc = [0]
            for bit in indicators:
                acc.append(acc[-1] | bit)
            if acc[-1]:
                rows.append(indicators.index(1))
        for bits in product(range(2), repeat=width):
            count = 0
            for code in product(rows, repeat=digits):
                index = sum(x * base**j for j,x in enumerate(code))
                if index < width and bits[index] and not any(bits[:index]):
                    count += 1
            assert count == int(any(bits))
print('All assignments for widths 1..8 and 1..3 digits passed')

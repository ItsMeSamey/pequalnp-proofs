from itertools import combinations, product


def check(length, digits, radix):
    # Positive clause on variables 1,...,length. Signed literals simply relabel truth bits.
    next_id = length + 1
    clauses = []
    rows = []
    for _ in range(digits):
        row = list(range(next_id, next_id + radix))
        next_id += radix
        rows.append(row)
        clauses.extend([(-a, -b) for a, b in combinations(row, 2)])
        prefix = row[0]
        for var in row[1:]:
            aux = next_id
            next_id += 1
            clauses.extend([(-prefix, aux), (-var, aux), (prefix, var, -aux)])
            prefix = aux
        clauses.append((prefix,))
    for index, key in enumerate(product(range(radix), repeat=digits)):
        guard = tuple(-row[choice] for row, choice in zip(rows, key))
        if index >= length:
            clauses.append(guard)
        else:
            clauses.append(guard + (index + 1,))
            clauses.extend(guard + (-earlier,) for earlier in range(1, index + 1))
    assert max(map(len, clauses)) <= max(3, digits + 1)
    for original in product((0, 1), repeat=length):
        count = 0
        for aux in product((0, 1), repeat=next_id - 1 - length):
            assignment = (False,) + original + aux
            count += all(any(assignment[abs(lit)] == (lit > 0) for lit in clause)
                         for clause in clauses)
        assert count == int(any(original))
    return 2 ** length


print(sum(check(length, digits, radix)
          for digits, radix, lengths in [(1, 1, [1]), (2, 2, [1, 2, 3, 4]),
                                         (3, 2, [2, 5]), (1, 3, [1, 2, 3])]
          for length in lengths), "first-true truth assignments with exhaustive auxiliaries")

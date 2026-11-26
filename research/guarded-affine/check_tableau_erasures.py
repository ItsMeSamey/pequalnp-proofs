"""Check inner-product projections on every hidden subspace through three pairs."""


def subspaces(bits):
    initial = frozenset({0})
    seen = {initial}
    queue = [initial]
    while queue:
        space = queue.pop()
        yield space
        for vector in range(1 << bits):
            if vector in space:
                continue
            larger = space | {vector ^ member for member in space}
            if larger not in seen:
                seen.add(larger)
                queue.append(larger)


def check(pairs):
    def inner_product(vector):
        return ((vector >> pairs) & vector).bit_count() % 2

    count = 0
    for space in subspaces(2 * pairs):
        dimension = len(space).bit_length() - 1
        isotropic = all(
            inner_product(x ^ y) == (inner_product(x) ^ inner_product(y))
            for x in space for y in space
        )
        representatives = {
            min(vector ^ member for member in space)
            for vector in range(1 << (2 * pairs))
        }
        rejected = sum(
            not any(inner_product(rep ^ member) for member in space)
            for rep in representatives
        )
        remaining = pairs - dimension
        expected = ((1 << (2 * remaining)) + (1 << remaining)) // 2 if isotropic else 0
        assert rejected == expected, (pairs, space, rejected, expected)
        count += 1
    return count


if __name__ == "__main__":
    for pairs, expected_count in enumerate((5, 67, 2825), start=1):
        count = check(pairs)
        assert count == expected_count, (pairs, count, expected_count)
        print(f"n={pairs}, {count} hidden subspaces checked")

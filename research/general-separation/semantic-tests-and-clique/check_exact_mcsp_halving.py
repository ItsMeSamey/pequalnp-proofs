"""Exhaust legal approximate modes and compare compact final equivalence to membership."""
from functools import lru_cache
from itertools import combinations_with_replacement, product


def column(book, bit):
    return sum((table >> bit) & 1 for table in book)


def legal_modes(ones, total):
    if 4 * ones <= total:
        return (0,)
    if 4 * ones >= 3 * total:
        return (1,)
    return (0, 1)


def verify(book, nbits, target):
    @lru_cache(None)
    def explore(live):
        if not live:
            return False
        modes = [legal_modes(column(live, i), len(live)) for i in range(nbits)]
        outcomes = set()
        for hypothesis in product(*modes):
            mismatch = next((i for i, vote in enumerate(hypothesis)
                             if vote != ((target >> i) & 1)), None)
            if mismatch is None:
                # Only the selected hypothesis and codebook enter the final test.
                outcomes.add(any(all(((candidate >> i) & 1) == vote
                                     for i, vote in enumerate(hypothesis))
                                 for candidate in book))
            else:
                wanted = (target >> mismatch) & 1
                new = tuple(t for t in live if (t >> mismatch) & 1 == wanted)
                assert 4 * len(new) <= 3 * len(live)
                outcomes.add(explore(new))
        assert len(outcomes) == 1
        result, = outcomes
        assert result == (target in live)
        return result
    assert explore(book) == (target in book)


def check():
    trials = 0
    for nbits in range(1, 4):
        tables = range(1 << nbits)
        for size in range(5):
            for book in combinations_with_replacement(tables, size):
                for target in tables:
                    verify(book, nbits, target)
                    trials += 1
    # The earlier gap learner may stop on these nonmembers; at 128 it must stop.
    for count in (32, 128):
        book = tuple(1 << i for i in range(count))
        assert 0 not in book
        assert all(16 * column(book, i) < count for i in range(count))
        if count == 128:
            assert all(64 * column(book, i) <= count for i in range(count))
        verify(book, count, 0)
    print(f'{trials} exhaustive codebook/target cases and two promise-stop controls passed')


if __name__ == '__main__':
    check()

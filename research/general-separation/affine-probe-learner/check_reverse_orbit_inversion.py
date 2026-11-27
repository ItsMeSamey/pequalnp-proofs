"""Bounded forward-label simulation against independent full halving streams."""
from itertools import permutations


def audit(perm, horizon, tie):
    size = len(perm)
    n = size.bit_length()-1
    powers = [tuple(range(size))]
    for _ in range(horizon):
        powers.append(tuple(perm[v] for v in powers[-1]))
    answers = [0]*size
    for i in range(n):
        queries = [tuple((v >> i) & 1 for v in row)
                   for row in reversed(powers[:horizon])]

        def play(labels):
            possible = list(range(size))
            predictions = []
            for ell, row in enumerate(queries):
                margin = 2*sum(row[s] for s in possible)-len(possible)
                predictions.append(tie if margin == 0 else int(margin > 0))
                if ell == len(labels):
                    break
                possible = [s for s in possible if row[s] == labels[ell]]
                assert possible
            return predictions

        genuine = []
        for seed in range(size):
            labels = [row[seed] for row in queries]
            predictions = play(labels)
            assert sum(a != b for a,b in zip(labels,predictions)) <= n
            genuine.append(predictions)
        errors = wrong = 0
        for x,y in enumerate(perm):
            votes = []
            for j in range(1,horizon+1):
                prefix = [(powers[j-ell-1][y] >> i) & 1 for ell in range(1,j)]
                guesses = play(prefix)
                seed = powers[horizon-j].index(x)  # audit only
                assert prefix == [row[seed] for row in queries[:j-1]]
                assert guesses == genuine[seed][:j]
                assert queries[j-1][seed] == ((x >> i) & 1)
                votes.append(guesses[-1])
            bit = int(2*sum(votes) > horizon)
            answers[x] |= bit << i
            errors += sum(v != ((x >> i) & 1) for v in votes)
            wrong += bit != ((x >> i) & 1)
        assert errors == sum(queries[j][s] != genuine[s][j]
                             for j in range(horizon) for s in range(size))
        assert wrong*horizon <= 2*errors <= 2*size*n
    rejected = [x for x,y in enumerate(perm) if perm[answers[x]] != y]
    assert rejected == [x for x in range(size) if answers[x] != x]
    assert len(rejected)*horizon <= 2*size*n*n


if __name__ == '__main__':
    for size in (2,4,8):
        tables = permutations(range(size)) if size < 8 else (
            tuple(range(8)), (1,2,3,4,5,6,7,0), (4,7,2,0,6,1,3,5))
        for table in tables:
            for horizon in (1,4,2*(size.bit_length()-1)**2+1):
                for tie in (0,1):
                    audit(table,horizon,tie)
    print('Original reverse-orbit streams agree.')

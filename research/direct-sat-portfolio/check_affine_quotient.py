"""Bounded independent truth-table and reconstructed-witness controls."""
import json
from random import Random
from affine_quotient import solve, estimate


def truth(n, gates, output, x):
    wires = [1] + [(x >> j) & 1 for j in range(n)]
    def read(word):
        return sum(value for j, value in enumerate(wires) if word >> j & 1) % 2
    for a, b in gates:
        wires.append(read(a) * read(b))
    return read(output)


def test(n, gates, output):
    expected = sum(truth(n, gates, output, x) for x in range(1 << n))
    bound = estimate(n, gates, output)
    result = solve(n, gates, output, budget=bound)
    assert result["count"] == expected and result["cost"]["units"] <= bound
    assert result["status"] == ("sat" if expected else "unsat")
    if expected:
        assert truth(n, gates, output, result["witness"])
    if bound > 1:
        assert solve(n, gates, output, budget=bound-1)["status"] == "skip"
    return result


def main():
    rng = Random(22141)
    routes = {"image":0, "quotient":0}
    for n in range(7):
        for _ in range(12):
            m = rng.randrange(6)
            gates = [(rng.randrange(1 << (n+j+1)),rng.randrange(1 << (n+j+1))) for j in range(m)]
            result = test(n, gates, rng.randrange(1 << (n+m+1)))
            routes[result["cost"]["method"]] += 1
    for _ in range(12):
        n = 8
        gates = []
        for i in range(4):
            prev = rng.randrange(1 << i) << (1+n)
            gates.append(((2 << (2*i)) ^ prev ^ rng.randrange(2),
                          (2 << (2*i+1)) ^ rng.randrange(2)))
        out = rng.randrange(1 << 13)
        result = test(n,gates,out)
        routes[result["cost"]["method"]] += 1
    n = 9
    gates = [(3,5),(8 ^ (2 << n),16),(32,64),(128,256)]
    changed = test(n,gates,1)
    assert changed["witness"] == 4 and changed["count"] == 512
    unsat = test(n,gates,0)
    assert unsat["cost"]["method"]=="quotient"
    n=8
    gates=[]
    for j in range(4):
        gates.append((2 << (2*j),2 << (2*j+1)))
    for j in range(4):
        dense = (15 ^ (1<<j)) << (n+1)
        second= (2 << (2*j)) ^ ((2 << (n+3+j)) if j else 0)
        gates.append((dense,second))
    full = test(n,gates,2 << (n+7))
    assert full["cost"]["rho"] == full["cost"]["tau"] == n
    print(json.dumps({"random_routes":routes,"transformed_nonidentity":changed,
                      "quotient_unsat":unsat,"dense_full_rank":full},sort_keys=True))


if __name__ == "__main__":
    main()

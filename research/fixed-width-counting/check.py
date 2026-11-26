"""Test both signed expansions using all assignments of seeded small instances."""
import itertools
import random

RNG = random.Random(84)

def character(mask, x):
    return 1 - 2 * ((mask & x).bit_count() % 2)

def cnf(clauses, wires):
    return int(all(any(wires[i] == b for i,b in clause) for clause in clauses))

def random_cnf(wires):
    return [[(RNG.randrange(wires),RNG.randrange(2)) for _ in range(3)]
            for _ in range(RNG.randrange(1,6))]

def check_fourier(n):
    rank = RNG.randrange(n+1)
    dim = n-rank
    rhs = RNG.randrange(1<<rank)
    terms = [(i,j) for i in range(n) for j in range(i+1) if RNG.randrange(2)]
    clauses = random_cnf(n)
    def phase(x):
        return 1-2*(sum((x>>i&1)*(x>>j&1) for i,j in terms)%2)
    points = [x for x in range(1<<n) if cnf(clauses, [(x>>i)&1 for i in range(n)])]
    expected = sum(phase(x) for x in points if (x&((1<<rank)-1))==rhs)
    values = [phase((y<<rank)|rhs) for y in range(1<<dim)]
    result = 0
    for a in range(1<<dim):
        coefficient = sum(f*character(a,y) for y,f in enumerate(values))
        for b in range(1<<rank):
            mask = (a<<rank)|b
            result += coefficient*character(b,rhs)*sum(character(mask,x) for x in points)
    assert result == (1<<n)*expected

def check_macros(n):
    macros = [random_cnf(n+j) for j in range(4)]
    direct = total = 0
    for x in itertools.product(range(2),repeat=n):
        values = list(x)
        for macro in macros:
            values.append(cnf(macro, values))
        direct += values[-1]
        for y in itertools.product(range(2),repeat=4):
            if y[-1] == 0:
                continue
            fixed = x+y
            required = [j for j,bit in enumerate(y) if bit]
            false = [j for j,bit in enumerate(y) if not bit]
            for mask in range(1<<len(false)):
                tested = required+[j for i,j in enumerate(false) if mask>>i&1]
                total += (-1)**mask.bit_count()*all(cnf(macros[j],fixed) for j in tested)
    assert total==direct

if __name__ == "__main__":
    for n in range(2,9):
        for _ in range(50):
            check_fourier(n)
    for n in range(1,5):
        for _ in range(25):
            check_macros(n)
    print("Verified 350 Fourier and 100 macro-circuit instances.")

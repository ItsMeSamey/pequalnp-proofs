from itertools import product
from random import Random
from unittest.mock import patch
from cnf_anf_prepass import consequences,replay,solve_cnf


def lifted(size):
    rows=[]
    for vertex in range(size):
        prev=(vertex-1)%size
        variables=(2*prev+1,2*prev+2,2*vertex+1,2*vertex+2)
        for bits in product((0,1),repeat=4):
            if ((bits[0]&bits[1])^(bits[2]&bits[3]))!=(vertex==0):
                rows.append(tuple(-i if b else i for i,b in zip(variables,bits)))
    return rows


def main():
    for size in (3,9,25):
        rows=lifted(size)
        conflict,eqs=consequences(2*size,rows,budget=20000)
        assert conflict is not None and replay(2*size,rows,0,1,conflict,budget=20000)
        assert not replay(2*size,rows,0,1,conflict^(conflict&-conflict),budget=20000)
        with patch('cnf_anf_prepass.minimize',side_effect=AssertionError("fallback entered")):
            assert solve_cnf(2*size,rows,budget=20000) is None
    rng=Random(793)
    for _ in range(70):
        n=rng.randrange(1,6)
        rows=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(4)))
              for _ in range(rng.randrange(7))]
        words=[x for x in range(1<<n) if all(any(bool(x&1<<(abs(l)-1))==(l>0) for l in c) for c in rows)]
        budget=rng.randrange(20)
        conflict,eqs=consequences(n,rows,budget=budget)
        assert all(replay(n,rows,a,b,s,budget=budget) and all((a&x).bit_count()%2==b for x in words)
                   for a,b,s in eqs)
        if conflict is not None:
            assert not words and replay(n,rows,0,1,conflict,budget=budget)
        value=solve_cnf(n,rows,budget=budget)
        assert value in words if words else value is None
    with patch('cnf_anf_prepass._violation',side_effect=AssertionError("expanded")):
        assert consequences(200,[range(1,201)],budget=17)==(None,())
    print("three AND-lifted odd Tseitin refutations, 70 brute CNFs, exact XOR proofs and wide skip passed")


if __name__=='__main__':
    main()

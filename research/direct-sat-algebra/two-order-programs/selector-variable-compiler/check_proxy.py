from itertools import product
from random import Random
from check import accepts, solve
from compiler import decode
from proxy import compile_proxy


def test():
    rng = Random(94199)
    cases = [(0, []), (0, [()]), (2, [()]), (3, [(1,1,-1),(-2,), (2,3)])]
    for n in range(1, 5):
        for _ in range(6):
            cases.append((n, [tuple(rng.choice((-1,1))*rng.randint(1,n)
                                   for _ in range(rng.randint(1,3)))
                             for _ in range(rng.randrange(8))]))
    checked = 0
    for n, rows in cases:
        for pinned in [False, True]:
            N, cs, selectors = compile_proxy(n, rows, pin_selectors=pinned)
            ternary = [row for row in rows if len(row)==3]
            m = len(ternary)
            u = n - len({abs(row[0]) for row in ternary})
            assert N == 6*m + 15*n + 6*u
            if n:
                assert len(cs) == 21*m + 40*n + 19*u + len(rows)-m + 2*n*pinned
            for word in range(1<<n):
                # Fix p,q to zero and r to each source bit. All helper values are forced.
                fixed = [(s if value else -s,) for i,triple in enumerate(selectors)
                         for s,value in zip(triple, (0,0,(word>>i)&1))]
                result = solve(N,cs+fixed,b=n,extract_arities=(3,),exponent_cap=0,
                               complete=False,orient=True,detect_blocks=True)
                assert result['status'] == ('sat' if accepts(rows,word) else 'unsat')
                if result['status']=='sat':
                    w=result['witness']
                    assert accepts(cs+fixed,w) and decode(w,selectors)==word
                checked+=1
    print(checked, 'physical fibers checked')


if __name__=='__main__':
    test()

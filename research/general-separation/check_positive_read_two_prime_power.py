"""Independent original-assignment oracle over Z/(3**k), using integer products."""
from itertools import product
from math import prod
from random import Random
from positive_read_two_prime_power import evaluate


def direct(clauses,point,k):
    return sum(prod(p if x else 1-p for p,x in zip(point,bits))
               for bits in product((0,1),repeat=len(point))
               if all(any(bits[i] for i in clause) for clause in clauses)) % 3**k


def check(clauses,point,k):
    expected=direct(clauses,point,k)
    res=evaluate(len(point),clauses,point,k)
    assert res['status']=='exact' and res['value']==expected,(clauses,point,k,res,expected)
    return res


def main():
    cases=0
    for k in (2,3):
        modulus=3**k
        for a in range(modulus):
            for b in (0,1,3,4,-4,modulus+2):
                check([(0,1),(0,1),(2,)], [a,b,7], k)
                cases+=1
    for k in (1,2,3,4,8):
        for a in (0,1,3,4,5,-4,10**36+6):
            assert check([(0,0)], [a], k)['value']==a%3**k
            check([(0,1),(1,2),(2,0)], [a,3**k,1-3**k],k)
    for clauses in ([],[()],[(0,),(0,)],[(0,1),(0,1)]):
        check(clauses,[0,1,99],5)
    rng=Random(71831)
    for _ in range(35):
        n=rng.randrange(1,7)
        clauses=[[] for _ in range(rng.randrange(1,6))]
        for i in range(n):
            for _ in range(rng.randrange(3)):
                rng.choice(clauses).append(i)
        k=rng.choice((2,3,5,7))
        check(clauses,[rng.randrange(-60,90) for i in range(n)],k)
    # Row and column edge covers of K2,2. Exactly two covers have two edges.
    graph=[(0,1),(2,3),(0,2),(1,3)]
    k=8
    z=check(graph,[9]*4,k)['value']
    assert z%81==0 and z//81%9==2
    m=3**k
    half=pow(2,-1,m)
    assert 16*check(graph,[half]*4,k)['value']%m==7
    res=check([(0,)],[4],3)
    budget=res['contractions']
    assert budget>0
    capped=evaluate(1,[(0,)],[4],3,max_contractions=budget-1)
    assert capped['status']=='unknown' and capped['reason']=='contraction_budget'
    assert capped['required']==budget and capped['available']==budget-1
    for n,clauses,point,k in [(1,[(0,0,0)],[1],2),(1,[(1,)],[0],2),
                              (2,[],[1],2),(1,[],[1],0)]:
        try:
            evaluate(n,clauses,point,k)
        except ValueError:
            continue
        raise AssertionError((n,clauses,point,k))
    print(f'{cases} residue-grid checks, higher precision, matchings and budget passed.')


if __name__=='__main__':
    main()

from itertools import product
from random import Random
from choice_cover_multi_xor import solve,solve_long_covers
from choice_cover_one_xor_check import instance


def check(n,groups,resources,equations):
    cnf = instance(groups,resources)
    def good(x):
        def value(lit):
            return ((x>>(abs(lit)-1))&1)^(lit<0)
        return (all(any(map(value,c)) for c in cnf) and
                all(sum(map(value,row))%2==rhs for row,rhs in equations))
    truth = any(good(x) for x in range(1<<n))
    answers = []
    for exact in (False,True):
        status,word,_ = solve(n,cnf,range(len(groups)),equations,exact=exact)
        assert status in ('SAT','UNSAT','UNKNOWN')
        if exact or status != 'UNKNOWN':
            assert truth == (status=='SAT'),(groups,resources,equations,status)
        assert (word is not None)==(status=='SAT')
        if word is not None:assert good(word)
        answers.append(status)
    return tuple(answers)


if __name__=='__main__':
    counts={}
    def run(*args):
        result=check(*args)
        counts[result]=counts.get(result,0)+1
        return result
    # Arbitrarily signed rows, outside variables, dummy rows and both fallbacks.
    for signs in product((-1,1),repeat=3):
        G=[[i*s for i,s in enumerate(signs,1)]]
        for a,b in product(range(2),repeat=2):
            run(3,G,{1:0,2:1,3:2},[([2],a),([3],b)])
    G=[[1,2,3]]; R={1:0,2:1,3:2}
    assert run(3,G,R,[([2],1),([3],0)])==('UNKNOWN','SAT')
    assert run(3,G,R,[([2],1),([3],1)])==('UNKNOWN','UNSAT')
    assert solve_long_covers(3,instance(G,R),[([2],1),([3],1)],exact=True)[0]=='UNSAT'
    rng=Random(7259)
    for _ in range(850):
        groups=[]; resources={};v=0
        for g in range(rng.randrange(5)):
            group=[]
            for i in range(rng.randint(1,3)):
                v+=1;group.append(rng.choice((-v,v)));resources[v]=rng.randrange(4)
            groups.append(group)
        n=v+rng.randrange(3)
        eq=[([rng.choice((-1,1))*rng.randint(1,n) for i in range(rng.randrange(7))] if n else [],
             rng.randrange(2)) for j in range(rng.randrange(5))]
        run(n,groups,resources,eq)
    # A shared free variable supplies one simultaneous two-row direction.
    assert run(2,[[1]],{1:0},[([2],1),([-2],0)])==('SAT','SAT')
    assert run(2,[[1]],{1:0},[([2],1),([-2],1)])==('UNSAT','UNSAT')
    print(sum(counts.values()),'brute-force CNF cases, status transitions',counts)

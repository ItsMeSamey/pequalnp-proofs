"""Direct original signed-CNF control with optional invertible violation-row mixing."""
from random import Random
from multi_producer_parity import compile_system,reference_join


def violations(clauses):
    rows=[]
    for clause in clauses:
        p={0}
        for l in clause:
            bit=1<<(abs(l)-1)
            q=p.copy() if l>0 else set()
            for mon in p:
                q.symmetric_difference_update([bit|mon])
            p=q
        rows.append(p)
    return rows


def check(n,clauses,mix):
    rows=violations(clauses)
    if mix and len(rows)>1:
        for i in range(len(rows)-1):
            rows[i]^=rows[i+1]
        rows[0],rows[-1]=rows[-1],rows[0]
    terms=sorted(set().union(*rows)-{0})
    net=compile_system(n,rows,0,[list(range(0,len(rows),2)),list(range(1,len(rows),2))],
                       [terms[::2],terms[1::2]])
    raw=lambda x:all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
    good={x for x in range(1<<n) if raw(x)}
    result=reference_join(net,budget=50000)
    assert result is not None
    count,w=result
    assert count==len(good) and (w in good and raw(w) if count else w is None)
    return count


if __name__=='__main__':
    rng=Random(8351)
    cases=[(0,[]),(0,[()]),(3,[(-1,-2),(-1,-3)]),(2,[(1,),(-1,)]),
           (3,[(1,-1),(2,2),(-2,3)]),(4,[(1,),(-2,)])]
    for _ in range(35):
        n=3
        clauses=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,4)))
                 for j in range(rng.randrange(1,4))]
        cases.append((n,clauses))
    for n,C in cases:
        assert check(n,C,False)==check(n,C,True)
    print('41 original signed CNFs; both unmixed and invertibly mixed charts matched raw counts and original witnesses')

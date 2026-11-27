"""Independent full-tree, packed-code, witness and pre-materialization controls."""
from functools import lru_cache
from itertools import product
from random import Random
from unittest.mock import patch
from controlled_code_tree_search import plan_and_solve
from check_controlled_code_blocks import apply,legal,triangle,triangle_reference


def span(cols):
    values={0}
    for col in cols: values |= {v^col for v in values}
    return values


def all_clocks(A,U,forms):
    """Enumerate every binary tree. Use explicit quotient cosets, not Gaussian rank."""
    n,k=len(A),len(U)
    data=span([(A[j]<<k)|sum(((f>>j)&1)<<i for i,(f,_) in enumerate(forms))
               for j in range(n)])
    def repr_(v): return min(v^w for w in data)
    pairs=[(repr_(1<<i),repr_(u<<k)) for i,u in enumerate(U)]
    full=(1<<k)-1
    @lru_cache(None)
    def side(s): return span([v for i,p in enumerate(pairs) if s>>i&1 for v in p])
    def rankwidth(s): return len(side(s)&side(full^s)).bit_length()-1
    @lru_cache(None)
    def trees(s):
        if s&(s-1)==0: return [4]
        term=len(span([p[1] for i,p in enumerate(pairs) if s>>i&1]))<<rankwidth(s)
        costs=[]
        free=s^(s&-s)
        left=free
        while left:
            right=s^left
            merge=1<<(rankwidth(left)+rankwidth(right))
            for a in trees(left):
                for b in trees(right): costs.append(min(term,a+b+merge))
            left=(left-1)&free
        return costs
    return trees(full)


def check(m,A,b,U,forms):
    n,k=len(A),len(U)
    ref=sum(legal(A,b,U,forms,x,y) for x in range(1<<k) for y in range(1<<n))
    result=plan_and_solve(m,A,b,U,forms,clock_cap=1000000)
    assert result.count==ref
    assert result.status==("SAT" if ref else "UNSAT")
    if ref: assert legal(A,b,U,forms,*result.witness)
    if result.strategy=="linear": return
    best=min(all_clocks(A,U,forms))
    assert result.clock==best and result.optimal
    with patch("controlled_code_tree_search.solve",side_effect=AssertionError("premature backend")):
        miss=plan_and_solve(m,A,b,U,forms,clock_cap=best-1)
        assert miss.status=="UNKNOWN" and miss.clock==best and miss.witness is None
    boundary=plan_and_solve(m,A,b,U,forms,clock_cap=best,decision_only=True)
    assert boundary.count==bool(ref)
    greedy=plan_and_solve(m,A,b,U,forms,clock_cap=1000000,exact_limit=0)
    assert greedy.count==ref and greedy.clock>=best


def main():
    tests=0
    for a,b,u,v,f,c,g,d in product((0,1),repeat=8):
        check(1,[a],b,[u,v],[(f,c),(g,d)])
        tests+=1
    rng=Random(5023)
    for _ in range(160):
        n,m,k=rng.randrange(5),rng.randrange(4),rng.randrange(1,6)
        check(m,[rng.randrange(1<<m) for _ in range(n)],rng.randrange(1<<m),
              [rng.randrange(1<<m) for _ in range(k)],
              [(rng.randrange(1<<n),rng.randrange(2)) for _ in range(k)])
        tests+=1
    for length in (2,3,5,8):
        m,A,b,U,q,_=triangle(length)
        n=len(A)
        B=[1<<j for j in range(n)]
        for _ in range(n*n*3):
            j,i=rng.sample(range(n),2)
            B[j]^=B[i]
        offset=rng.randrange(1<<n)
        A2=[apply(A,col) for col in B]
        b2=b^apply(A,offset)
        forms=[(sum(((v&col).bit_count()%2)<<i for i,col in enumerate(B)),
                c^((v&offset).bit_count()%2)) for v,c in q]
        order=rng.sample(range(m),m)
        u2=[U[j] for j in order]
        q2=[forms[j] for j in order]
        result=plan_and_solve(m,A2,b2,u2,q2,clock_cap=1<<40,exact_limit=8)
        assert result.count==triangle_reference(length)
        x,y=result.witness
        assert legal(A,b,U,q,sum(((x>>i)&1)<<j for i,j in enumerate(order)),apply(B,y)^offset)
        with patch("controlled_code_tree_search.solve",side_effect=AssertionError("bad cap")):
            for planning in (0,1,32):
                low=plan_and_solve(m,A2,b2,u2,q2,clock_cap=0,planning_cap=planning)
                assert low.status=="UNKNOWN"
        print("triangle",length,result.strategy,result.clock,result.planning_units)
    assert plan_and_solve(0,[],0,[],[],clock_cap=0).count==1
    try: plan_and_solve(1,[1],0,[1],[(1,0)],clock_cap=-1)
    except ValueError: pass
    else: raise AssertionError("negative cap accepted")
    print("source cases",tests,"plus four dense affine recodings")
if __name__=="__main__": main()

"""Independent exhaustive truth vectors for the rank-aware remote cover."""
from itertools import product
from source_remote_pivot_rank import solve
from source_remote_pivot_reach import solve as greedy

def ref(rows,n):
    b=[r for r in rows if len(r)<3]
    t=[r for r in rows if len(r)==3]
    def passes(word,row):
        return any((word>>(abs(x)-1)&1)==(x>0) for x in row)
    words=[w for w in range(1<<n) if all(passes(w,row) for row in b)]
    cols=[sum((not passes(w,row))<<i for i,w in enumerate(words)) for row in t]
    basis={}
    for col in cols:
        while col and col.bit_length() in basis: col^=basis[col.bit_length()]
        if col: basis[col.bit_length()]=col
    return len(basis),{w for w in words if all(passes(w,row) for row in t)}

def check(rows,n,ranked=True):
    rank,valid=ref(rows,n)
    r=solve(n,rows)
    assert r['status']==('SAT' if valid else 'UNSAT'),r
    if valid:
        t=r['true_variables']
        assert tuple(sorted(set(t)))==t and all(1<=v<=n for v in t)
        assert sum(1<<(v-1) for v in t) in valid
    else: assert r['true_variables'] is None
    if ranked: assert r['metrics']['rank']==rank,(r,rank)
    return r

def main():
    gap=[(1,3,4),(-1,3,4),(2,3,4),(-2,3,4),(1,5,6),(2,7,8)]
    r=check(gap,8)
    assert tuple(r['pivots'])==(1,2) and tuple(r['metrics']['gains'])==(3,2)
    assert tuple(greedy(8,gap)['pivots'])==(3,1,2)
    print('strict pivot reduction 3 to 2, rank 5, marginal gains 3 and 2')
    B=[(1,2),(-2,3),(-3,4),(-4,1),(-1,3)]
    T=[(1,-2,3),(-1,2,3),(2,3,-4),(1,3,4),(-1,-3,-4)]
    for mask in range(32):
        check(T+[row for j,row in enumerate(B) if mask>>j&1],4)
    U=[(a,2*b,3*c) for a,b,c in product((1,-1),repeat=3)]
    check(U,3)
    for cap in ('rank_cap','discovery_cap','branch_cap'):
        ans=solve(8,gap,**{cap:0})
        assert ans['status']=='UNKNOWN' and ans['true_variables'] is None
    for pins in (((3,1),),((3,0),(3,1))):
        ans=solve(8,gap,source_pins=(iter(p) for p in pins))
        assert ans['status']==('SAT' if len(pins)==1 else 'UNSAT')
        if len(pins)==1:
            selected=set(ans['true_variables'])
            assert 3 in selected and all(any((abs(x) in selected)==(x>0) for x in row) for row in gap)
    print('32 binary backgrounds vs complete GF2 truth-vector ranks, rank-8 UNSAT, three caps and nested pin replay passed')
if __name__=='__main__': main()

from barrington_cnf_rail import IDENT,RHO,compile_cnf,evaluate,find_witness
from commuting_toggle_rails import compose,inverse


def run():
    cases = [
        (0,[]), (0,[()]), (1,[(1,),(-1,)]),
        (2,[(a,b) for a in (1,-1) for b in (2,-2)]),
        (3,[(1,2,3),(-1,),(-2,),(-3,)]),
        (2,[(1,)]), (2,[(1,2),(-1,-2)]), (3,[(1,-2,3),(-1,2)]),
        (2,[(1,-1),(2,-2)])]
    for n,clauses in cases:
        gates,tail=compile_cnf(n,clauses)
        hits=[]
        for x in range(1<<n):
            truth=all(any(bool((x>>(abs(l)-1))&1) == (l>0) for l in c) for c in clauses)
            p=evaluate(gates,tail,x)
            assert p==(RHO if truth else IDENT)
            closed=compose(inverse(RHO),p)
            assert sum(v==i for i,v in enumerate(closed))==5*int(truth)
            if truth:
                hits.append(x)
        witness=find_witness(n,clauses)
        assert (witness is None)==(not hits)
        if witness is not None:
            x,s=witness
            assert x in hits and 0<=s<5 and compose(inverse(RHO),evaluate(gates,tail,x))[s]==s
        print(n,len(clauses),len(gates),len(hits),witness)


if __name__=='__main__':
    run()

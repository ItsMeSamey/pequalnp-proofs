"""Independent SCC-pin oracle and original NAND cascading-promotion checks."""
from itertools import product
from unittest.mock import patch
import check_ordered_rows_04 as small
import indexed_ordered_row_csp as indexed
import ordered_row_csp as original


def valid(w,rows):
    return all(any(w[abs(l)-1]==(l>0) for l in c) for c in rows)


def pins_test():
    # Nontrivial mutual implication SCCs, hidden intermediate chains, unit,
    # and disconnected variable. Enumerate every subset of terminal literals,
    # including pins containing both polarities and repeated pins.
    base=[(-1,2),(-2,1),(-2,3),(-3,4),(-4,5),(-5,4),(-4,-6),(7,),(-7,8)]
    for rows in (base,base+[(1,),(6,)],base+[()]):
        n=9
        words=[w for w in product(range(2),repeat=n) if valid(w,rows)]
        ix=indexed.PinIndex(n,rows)
        assert ix.consistent == bool(words)
        terminals=(1,-1,6,-6,8,-8,9,-9)
        for flags in product(range(2),repeat=len(terminals)):
            units=tuple(l for l,b in zip(terminals,flags) if b)
            answer=any(all(w[abs(l)-1]==(l>0) for l in units) for w in words)
            assert ix.compatible(iter(units+units)) == answer


def physical(depth, link, last, cap):
    n=2*depth+1
    gates,ports=[],[]
    def gate(a,b):
        gates.append((a,b))
        return n+len(gates)-1
    for i in range(depth):
        x,p=2*i,2*i+1
        o=gate(x,p)
        e=gate(o,p)
        t=gate(e,gate(p,p))
        ports.append((o,e,t))
    guard=n
    rows=[(guard,)]+[(guard,v+1) for vs in ports for v in vs]
    if link:
        rows.append((ports[0][2]+1,))
        for pre,post in zip(ports,ports[1:]):
            rows.extend(((post[2]+1,pre[0]+1),(post[2]+1,pre[1]+1)))
        if last is not None:
            rows.append(((ports[-1][2]+1)*(1 if last else -1),))
    raw_ok=lambda w: valid(small.replay(w,gates),rows)
    feasible=any(raw_ok(w) for w in product(range(2),repeat=n))
    ans,ref,model=original.solve(n,gates,clauses=rows,max_bad=cap)
    state,stats,raw=indexed.solve(n,gates,clauses=rows,max_bad=cap)
    assert state==ans
    if state=='skip':
        assert not link and cap<depth and raw is None
    else:
        assert state==('sat' if feasible else 'unsat')
        if feasible:
            assert raw_ok(raw) and raw_ok(model)
            if link:
                assert stats['bad']==0 and stats['promoted']==depth
        else:
            assert raw is None


def main():
    pins_test()
    for link,last,cap in ((True,None,0),(True,True,0),(True,False,0),
                          (False,None,3),(False,None,4)):
        physical(4,link,last,cap)
    # Reuse the independent exact-candidate and physical row oracles. The
    # patched frontend leaves the original physical NAND verifier untouched.
    with patch.object(small,'solve',indexed.solve):
        small.main()
    print('768 signed pin vectors, four-stage promotion, original min/median/caps')


if __name__=='__main__':
    main()

"""Direct Boolean cube on original labels for binary-background SAT and counting."""
from itertools import product
import cnf_binary_background_rank as decision
import cnf_binary_background_count as counting
from read_two_ring_nonzero import compile_nonzero


def ok(row,s):
    return any((abs(l) in s)==(l>0) for l in row)


def rank(cols):
    values={0}
    for x in cols:
        values|={v^x for v in values}
    return len(values).bit_length()-1


def test(n,rows,want=None,caps=False):
    named=sorted({abs(l) for row in rows for l in row})
    cube=[{v for v,b in zip(named,bits) if b} for bits in product((0,1),repeat=len(named))]
    binary=[r for r in rows if len(set(r))<=2]
    cubic=[r for r in rows if len(set(r))==3]
    models=[s for s in cube if all(ok(c,s) for c in rows)]
    bg=[s for s in cube if all(ok(c,s) for c in binary)]
    def cols(cs,assignments):
        return [sum((not ok(c,s))<<j for j,s in enumerate(assignments)) for c in cs]
    expected=rank(cols(cubic,bg))
    p=decision.project(n,rows)
    assert p.feasible==bool(bg)
    if bg:
        assert p.rank==expected and all(ok(c,set(p.origin_true_ids)) for c in binary)
        assert [s for s in bg if all(ok(rows[i],s) for i in p.indices)]==models
        assert all(set(p.clauses[j])==set(rows[i]) for j,i in enumerate(p.indices))
    d=decision.solve(n,rows)
    assert d['status']==('nonzero' if models else 'zero')
    if models:
        assert set(d['true_ids']) in models
    c=counting.solve(n,rows)
    assert c['status']==d['status']
    mantissa,free=c['count']
    assert (mantissa<<free)==len(models)<<(n-len(named))
    if models:
        assert set(c['true_ids']) in models
    if want:
        assert (rank(cols(cubic,cube)),expected,len(models))==want
    if caps:
        for fun,budget,field in [(counting.solve,'max_terms','terms'),(decision.solve,'max_branches','branches')]:
            complete=c if field=='terms' else d
            charged=complete[field]
            assert charged>0
            fail=fun(n,rows,**{budget:charged-1})
            assert fail['status']=='unknown' and fail['required']==charged
            assert fun(n,rows,**{budget:charged})['status']==complete['status']
    return c,models


def main():
    original=[(-2,3),(1,2,3),(1,2,-3),(1,-2,-3),(1,4,5),(1,4,-5),(1,-4,6),(1,-4,-6)]
    test(6,original,(7,6,24),True)
    test(4,[(1,),(-1,),(-1,3,4)])
    test(6,[(1,),(-2,3),(2,-3,4)])
    path=[(-i,-i-1) for i in range(1,9)]+[(1,4,7)]
    forest,_=test(10,path,caps=True)
    cyclic,_=test(10,path+[(-1,-9)],caps=True)
    assert forest['mode']==cyclic['mode']=='forest'
    huge=1<<400
    wide=counting.solve(huge,[(1,2,3,huge)])
    assert wide['backend']=='unrestricted_span' and wide['count']==(15,huge-4)
    assert any(x in wide['true_ids'] for x in (1,2,3,huge))
    assert forest['feedback']==0 and cyclic['feedback']>0
    for m in (4,5):
        q,z=m+2,m+3
        family=[(-1,-x) for x in range(2,q)]+[(q,z)]+[(-1,-q,x) for x in range(2,q)]
        restricted,models=test(z,family)
        assert restricted['count']==(3*(1<<m)+1,0) and restricted['rank']==1
        assert restricted['mode']=='forest' and 0<restricted['terms']<=2*(m+4)
    physical(original)
    print('Ranks 7/6, 24 models, forest/cycle costs and original physical witness passed.')


def physical(rows):
    from ring_image_binary_background import count
    raw=compile_nonzero(6,rows)
    args=tuple(raw[k] for k in ('n','clauses','point','k'))
    result=count(*args)
    assert (result['status'],result['count'])==('nonzero',24)
    witness={i for i,b in enumerate(result['assignment'],1) if b}
    assert all(ok(c,witness) for c in rows)
    assert result['value']==24*pow(-15,raw['expanded_edges'],3**raw['k'])%3**raw['k']
    assert count(*args,max_round=0)['status']=='unknown'
    assert count(*args[:-1],args[-1]+(1<<1000))['status']=='off_image'


if __name__=='__main__':
    main()

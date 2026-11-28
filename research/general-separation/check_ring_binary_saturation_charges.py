"""Original signed-CNF witness oracle plus audit of charged nested attempts."""
from itertools import product
from read_two_ring_nonzero import compile_nonzero
from ring_image_binary_saturation import count


def fixture(n,rows):
    r=compile_nonzero(n,rows)
    args=tuple(r[k] for k in ('n','clauses','point','k'))
    models={x for x in product(range(2),repeat=n)
            if all(any(x[abs(l)-1]==(l>0) for l in row) for row in rows)}
    return args,models,r['expanded_edges']


def verify(case,result):
    args,models,e=case
    assert result['status']==('nonzero' if models else 'zero')
    assert result['count']==len(models)
    assert result['value']==len(models)*pow(-15,e,3**args[-1])%3**args[-1]
    if models:
        assert tuple(result['assignment']) in models
    assert set(result['charges'])=={'saturated_terms','background_terms','span_terms','determinants'}


def main():
    rows=[(1,2,3),(1,2,-3)]
    case=fixture(3,rows)
    args=case[0]
    exhausted=count(*args,max_round=2)
    assert exhausted['status']=='unknown' and exhausted['reason']=='round_limit'
    assert exhausted['attempts']==2 and exhausted['charges']['saturated_terms']==3
    assert exhausted['charges']['background_terms']>=3 and exhausted['charges']['span_terms']>=3
    ans=count(*args)
    verify(case,ans)
    assert ans['route']=='saturated' and any(set(r)=={1,2} for r in ans['derived'])
    # The binary residual is x1 OR x2. Its graph is a tree, and
    # x3 is free. One full count and two prefix probes cost one term
    # each. The final quota of four therefore consumes three terms.
    assert ans['mode'] == 'forest' and ans['rank'] == ans['feedback'] == 0
    assert (ans['attempts'], ans['last_quota'], ans['terms']) == (3, 4, 3)
    assert ans['charges']['saturated_terms'] == 1 + 2 + 3
    for key in ('background_terms', 'span_terms', 'determinants'):
        assert ans['charges'][key] == exhausted['charges'][key]
    assert all(ans['charges'][k]>=v for k,v in exhausted['charges'].items())
    for n,rows,cap,route in [(0,[],0,'original'),(0,[()],0,'saturated'),
                             (4,[(1,2,3,4)],None,'wide_delegate')]:
        case=fixture(n,rows)
        ans=count(*case[0],max_round=cap)
        verify(case,ans)
        assert ans['route']==route
    print('Physical saturation, fallback and wide delegation, witness, charges and residues passed.')


if __name__=='__main__':
    main()

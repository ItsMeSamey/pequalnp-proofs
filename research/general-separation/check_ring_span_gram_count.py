"""Four-field public interface vs enumeration of all original signed-CNF witnesses."""
from itertools import product
from read_two_ring_nonzero import compile_nonzero
from ring_image_span_gram_count import count


def fixture(n,clauses):
    r=compile_nonzero(n,clauses)
    fields=tuple(r[k] for k in ('n','clauses','point','k'))
    models={bits for bits in product(range(2),repeat=n)
            if all(any(bits[abs(l)-1]==(l>0) for l in row) for row in clauses)}
    return fields,models,r['expanded_edges']


def verify(data,result):
    fields,models,e=data
    assert result['count']==len(models)
    assert result['status']==('nonzero' if models else 'zero')
    assert result['value']==pow(-15,e,3**fields[-1])*len(models)%3**fields[-1]
    if models:
        assert tuple(result['assignment']) in models


def main():
    rows=[]
    for i in range(1,5):
        j=i%4+1
        rows.extend(((i,j),(-j,-i)))
    data=fixture(4,rows)
    fields=data[0]
    gram=count(*fields,max_terms=0,max_determinants=100)
    verify(data,gram)
    assert gram['backend']=='gram' and gram['terms']==0 and gram['determinants']>1
    fallback=count(*fields,max_determinants=1)
    verify(data,fallback)
    assert fallback['backend']=='span' and fallback['determinants']==1
    assert fallback['gram_attempt']['reason']=='determinant_budget'
    assert 0<fallback['terms']<=fallback['raw_term_bound']
    denied=count(*fields,max_terms=0,max_determinants=1)
    assert denied['status']=='unknown' and denied['reason']=='count_budget'
    assert denied['terms']==0 and denied['determinants']==1
    for n,cs in [(4,[(4,),(-4,2),(1,-1)]),(2,[()]),(2,[]),(0,[]),(1,[(1,),(-1,)])]:
        f=fixture(n,cs)
        verify(f,count(*f[0]))
    nv,c,p,k=fields
    assert count(nv,c,p,-1)['status']=='off_image'
    print('Physical exact counts, original witnesses, partial Gram fallback and dual refusal passed.')


if __name__=='__main__':
    main()

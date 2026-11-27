"""Raw ordered image and direct original witness-language replay; no ring evaluation."""
from itertools import product
from read_two_ring_image import recover
from read_two_ring_nonzero import compile_nonzero


def args(raw):
    return raw['n'],raw['clauses'],raw['point'],raw['k']


def models(n,clauses):
    return {bits for bits in product(range(2),repeat=n)
            if all(any(bits[abs(l)-1]==(l>0) for l in c) for c in clauses)}


def main():
    for n,cs in [(0,()),(0,((),)),(1,((1,),(-1,))),
                 (2,((2,-1,2),(2,-1,2))), (2,((1,-1),)),(1,())]:
        raw=compile_nonzero(n,cs)
        nv,c,p,k=args(raw)
        got=recover(nv,[list(row) for row in c],list(p),k)
        assert got==(n,tuple(tuple(dict.fromkeys(row)) for row in cs))
        assert models(*got)==models(n,cs)
        assert args(compile_nonzero(*got))==args(raw)
        assert recover(nv,c,p,1<<10000) is None
        assert recover(nv,c,p[:-1],k) is None
        assert recover(nv,c+((nv,),),p,k) is None
        assert recover(nv,c,p[:-1]+(-1,),k) is None
        assert recover(nv,c,p[:-1]+(p[-1]+3**k,),k) is None
        assert recover(nv,c,p,False) is None
        assert recover(nv,{},p,k) is None
        if len(set(c))>1:
            j=next(i for i in range(len(c)) if c[i]!=c[0])
            swapped=list(c)
            swapped[0],swapped[j]=swapped[j],swapped[0]
            assert recover(nv,swapped,p,k) is None
    selector=compile_nonzero(1,[(1,)],selectors={1:-1})
    assert recover(*args(selector)) is None
    print('Six ordered image round trips, original certificate sets and raw tamper tests passed.')


if __name__=='__main__':
    main()

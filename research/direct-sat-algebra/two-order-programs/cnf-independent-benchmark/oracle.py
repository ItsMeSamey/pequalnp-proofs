from collections import Counter
from corpus import corpus

def accepted(rows,w):
    return all(any(((w>>(abs(x)-1))&1)==int(x>0) for x in row) for row in rows)

def oracle(label,n,rows,basis):
    if n<=12:
        words=[w for w in range(1<<n) if accepted(rows,w)]
        if basis!='enumerate':
            assert bool(words)==(basis in ('diagonal','all-zero'))
        return {'sat':bool(words),'models':len(words),'evidence':'exhaustive','words':1<<n}
    if basis in ('diagonal','all-zero'):
        d=int(label.split('-')[1])
        w=sum(1<<(i*d+i) for i in range(d)) if basis=='diagonal' else 0
        assert accepted(rows,w)
        return {'sat':True,'witness':w,'evidence':basis}
    if basis not in ('odd-charge','pigeonhole','edge-conflict'):raise ValueError(basis)
    return {'sat':False,'evidence':basis}

if __name__=='__main__':
    z=Counter()
    for k,n,f,b in corpus():
        d=oracle(k,n,f,b)
        z[k.split('-')[0],d['sat']]+=1
    print(z)

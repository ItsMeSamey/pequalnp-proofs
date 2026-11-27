"""Exact signed counting on acyclic aggregate/polynomial interfaces."""
from itertools import product
from random import Random
from original_dag_quadratic import gauss


def polyval(p,x):
    return sum(x&t==t for t in p)%2


def testval(test,x):
    vs,tab=test
    idx=sum((x>>v&1)<<i for i,v in enumerate(vs))
    return tab>>idx&1


def check(q,gates):
    # Interface b_i has coordinate q+i. Each gate describes its original function.
    n=q+len(gates)
    direct=0
    for x in range(1<<q):
        w=x
        for i,(kind,sign,body) in enumerate(gates):
            if kind=='poly':z=polyval(body,w)
            else:z=all(testval(t,w) for t in body)
            w|=(z^sign)<<(q+i)
        direct+=w>>(n-1)&1
    total=0; calls=0; sizes=[]; negs=0
    for selectors in product(range(2),repeat=len(gates)):
        phase=set()
        local=[((n-1,),2)]
        for i,((kind,sign,body),sel) in enumerate(zip(gates,selectors)):
            b=q+i
            if kind=='poly':
                if sel:
                    phase.symmetric_difference_update(body)
                    phase.symmetric_difference_update((1<<b,))
                    if sign:phase.symmetric_difference_update((0,))
            elif sel:
                # Active tests are conjoined; their multiplier is (-1)^(1+b+sign).
                local.extend(body)
                phase.symmetric_difference_update((1<<b,))
                if not sign:phase.symmetric_difference_update((0,))
            else:
                local.append(((b,),1<<sign))
        guards=[sum(1<<v for v in vs) for vs,_ in local]
        U=0
        for j in range(n):
            cand=U|1<<j
            if all((cand&g).bit_count()<=1 for g in guards) and all(
                    (cand&t).bit_count()<=2 for t in phase):U=cand
        sizes.append(U.bit_count())
        outside=((1<<n)-1)^U
        w=outside
        while True:
            pins=0; values=w; valid=True
            for test,g in zip(local,guards):
                v=g&U
                ok0=testval(test,w)
                ok1=testval(test,w|v)
                if not(ok0 or ok1):valid=False;break
                if ok0!=ok1:
                    if pins&v and bool(values&v)!=bool(ok1):valid=False;break
                    pins|=v
                    if ok1:values|=v
            if valid:
                free=U^pins
                p=set()
                for t in phase:
                    if not t&~(values|free):p.symmetric_difference_update((t&free,))
                count=gauss(p,free)
                if n<=10:
                    z=free
                    brute=0
                    while True:
                        brute+=(-1)**polyval(phase,values|z)
                        if not z:break
                        z=(z-1)&free
                    assert brute==count
                total+=count
                negs+=count<0
                calls+=1
            if not w:break
            w=(w-1)&outside
    denom=1<<sum(kind=='poly' for kind,_,_ in gates)
    assert total==denom*direct
    return direct,min(sizes),max(sizes),calls,negs


if __name__=='__main__':
    rng=Random(3771)
    for i in range(30):
        q=4;g=[]
        for t in range(1+i%4):
            n=q+t
            if rng.randrange(2):
                body={sum(1<<j for j in rng.sample(range(n),rng.randrange(min(n,4)+1))) for _ in range(5)}
                g.append(('poly',rng.randrange(2),body))
            else:
                body=[]
                for _ in range(3):
                    vs=tuple(rng.sample(range(n),rng.randrange(min(n,3)+1)))
                    body.append((vs,rng.randrange(1<<(1<<len(vs)))))
                g.append(('agg',rng.randrange(2),body))
        check(q,g)
    quadratic=[('poly',0,{3,6,12,24,48,33})]
    ans=check(6,quadratic)
    assert ans[1]==7
    print('interleaved quadratic',ans)
    mixed=[('agg',1,[((0,1),8),((1,2),14)]),
           ('poly',0,{5,1<<4,3<<2}),
           ('agg',0,[((4,5),6),((2,3),14)])]
    print('shared signed tests',check(4,mixed))
    # Three clique bits and six private bits; each cubic has two private endpoints.
    p={(1<<(i%3))|(1<<(3+i))|(1<<(3+(i+1)%6)) for i in range(6)}
    clique=[('poly',0,p),('agg',0,[((0,1,2),0xfe),((9,),2)])]
    print('cubic with clique guard',check(9,clique))
    # Private-first order certifies all six private variables in every term.
    # The final aggregate reads one test per clique edge, plus a shared interface bit.
    from itertools import combinations
    p={(1<<(6+i%4))|(1<<i)|(1<<((i+1)%6)) for i in range(6)}
    tests=[((a,b),14) for a,b in combinations(range(6,10),2)]+[((10,),2)]
    ans=check(10,[('poly',0,p),('agg',0,tests)])
    assert ans[1]>=6
    print('all clique-edge tests and private-first order',ans)
    print('30 seeded systems passed')

from itertools import product
from random import Random
from clause_rank_drop_hybrid import count
from clause_rank_drop import count as no_exceptions

def subspaces(n):
    spaces={frozenset([0])}
    for v in range(1,1<<n):
        spaces.update(frozenset(W|{x^v for x in W}) for W in list(spaces))
    return spaces

def test(n,cs,pins,check_opt=False):
    cells=[sum(1<<(abs(l)-1) for l in c) for c in cs]
    words={x for x in range(1<<n) if all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs)
           and all((x&m).bit_count()%2==b for m,b in pins)}
    for merge in (False,True):
        val,x,st=count(n,cs,pins,group_equal=merge)
        other,_,raw=count(n,cs,pins,group_equal=merge,prune=False)
        assert other==val and raw["optimum"]==st["optimum"]
        assert val==len(words) and (x in words if words else x is None)
        if check_opt:
            assert not pins
            costs={}
            for j,(c,s) in enumerate(zip(cs,cells)):
                key=s if merge else (s,j)
                costs.setdefault(key,set()).add(tuple(sorted(c)))
            expected=min((len(W).bit_length()-1)+sum(len(vals).bit_length() for key,vals in costs.items()
                if len([a for a in W if not a & ~(key if merge else key[0])])*2 < 1<<(key if merge else key[0]).bit_count())
                for W in subspaces(n))
            assert expected==st['optimum'],(cs,expected,st)
            if expected:assert count(n,cs,pins,cap=expected-1,group_equal=merge)[0] is None

if __name__=='__main__':
    rng=Random(16009); cases=0
    for n in range(1,5):
        for _ in range(35):
            cs=[[i*rng.choice((-1,1)) for i in rng.sample(range(1,n+1),rng.randint(1,n))]
                for j in range(rng.randrange(7))]
            test(n,cs,[],True);cases+=1
            test(n,cs,[(rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(4))]);cases+=1
    for cs in ([()],[(1,-1)],[(1,),(-1,)]):test(1,cs,[])
    m=5;n=1+2*m
    cs=[(1,j) for j in range(2,2+m)]+[(1,*range(2+m,2+2*m))]
    answer,x,stats=count(n,cs)
    assert answer==(1<<(2*m))+(1<<m)-1 and stats['optimum']==2
    assert no_exceptions(n,cs,optimal=True)[2]['codimension']==m
    # Four distinct forbidden points in rank 6: ungrouped p=4, grouped p=3.
    cs=[tuple(-i if j>>(i-1)&1 else i for i in range(1,7)) for j in range(4)]
    for merge,opt in [(False,4),(True,3)]:
        num,_,st=count(6,cs,group_equal=merge)
        assert (num,st['optimum'])==(60,opt)
    print(cases,'random instances both conventions, 140 exhaustive subspace minima; boundary and separation fixtures passed')

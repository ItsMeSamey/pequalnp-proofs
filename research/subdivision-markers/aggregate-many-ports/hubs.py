"""Compare full child tables with an exception-capped star merge."""
from itertools import product
from random import Random
from baseline import canonical, family
from check import assess

def merge(states,options,port,budget):
    out={}
    for (a,b,t,S),used in states.items():
        for (f,g),score,L,charge in options:
            count=used+charge
            if count>budget:
                continue
            add=tuple(S)+((port,) if len(L)==2 else ())
            new=canonical(add)
            if len(new)!=len(add):
                continue
            key=(a^(port if f else 0),b^(port if g else 0),t^score,new)
            out[key]=min(count,out.get(key,count))
    return out

def main():
    rng=Random(88221)
    queries=0
    for trial in range(60):
        k=trial%3
        allstates={(0,0,0,()):0}
        limited=allstates.copy()
        for j in range(rng.randrange(4,10)):
            d=rng.randrange(1,4)
            n=rng.randrange(1,5)
            cols=tuple(rng.randrange(1<<d) for _ in range(n))
            tags=tuple((rng.randrange(1<<k),rng.randrange(1<<k)) for _ in cols)
            p=rng.randrange(1,1<<d)
            port=rng.randrange(1,4)
            _,chart=family(cols,tags,(p,))
            baseline={assess(cols,tags,(p,),colors) for colors,score in chart.values()}
            full={y for c in product(range(4),repeat=n) if (y:=assess(cols,tags,(p,),c)) is not None}
            normal=tuple((*o,0) for o in full)
            restricted=tuple((*o,int(o not in baseline)) for o in full)
            allstates=merge(allstates,normal,port,k)
            limited=merge(limited,restricted,port,k)
        for T in [(),(1,),(2,),(3,),(1,2)]:
            def good(states):
                return {(a,b,t) for (a,b,t,S) in states if len(canonical(S+T))==len(S)+len(T)}
            assert good(allstates)==good(limited)
            queries+=len(good(limited))
    print('60 stars of 4–9 limbs, score/imbalance/test witnesses',queries)

if __name__=='__main__':
    main()

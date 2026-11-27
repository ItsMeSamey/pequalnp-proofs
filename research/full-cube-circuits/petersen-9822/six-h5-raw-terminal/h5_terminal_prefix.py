"""Minimum extra terminal ORs on a fixed bank of leaky monotone prefix signals."""
from functools import lru_cache

def finish(bank, positives, negatives, hidden=None):
    pfull=(1<<positives)-1
    nfull=(1<<negatives)-1
    if positives<1 or negatives<1 or any(not 0<=p<=pfull or not 0<n<=nfull for p,n in bank):
        raise ValueError('expected nonempty extremal classes and leaky signals')
    if hidden is not None and len(hidden)!=len(bank):raise ValueError('invalid support flags')
    required=pfull if hidden is None else pfull|(1<<positives)
    coverage=[p|((1<<positives) if hidden is not None and hidden[i] else 0) for i,(p,n) in enumerate(bank)]
    @lru_cache(None)
    def cheapest(ids):
        all_hits=0
        for i in ids:all_hits|=coverage[i]
        if all_hits!=required:return None
        @lru_cache(None)
        def cover(missing):
            if not missing:return ()
            bit=missing&-missing
            best=None
            for i in ids:
                p=coverage[i]
                if p&bit:
                    tail=cover(missing&~p)
                    if tail is not None and (best is None or len(tail)+1<len(best)):
                        best=(i,)+tail
            return best
        return cover(required)
    def eligible(allowed):
        return tuple(i for i,(_,n) in enumerate(bank) if coverage[i] and not n&~allowed)
    best=None
    for left in range(1<<(negatives-1)):
        a=cheapest(eligible(left))
        if a is None:continue
        b=cheapest(eligible(nfull^left))
        if b is not None and (best is None or len(a)+len(b)<len(best[0])+len(best[1])):
            best=a,b
    return None if best is None else (len(best[0])+len(best[1])-2,*best)

"""Replay a next round from true previous scores, pointwise clause conflicts and raw pins."""
from collections import Counter
from itertools import combinations

class Missing(Exception):
    pass

def replay(clauses,P,h,old_score,*,work_cap,next_score=None,pin_count=None,bicliques=(),
           row_cap=None):
    """work_cap limits algebraic steps globally; row_cap separately bounds emitted masks.
    After algebra exhaustion, further candidates may use explicitly priced next_score.
    Callback None values mean unavailable. Signed pins use 1-based variable numbers.
    """
    cs=tuple(frozenset(row) for row in clauses)
    q=len(cs)
    if min(P,work_cap)<0 or h<0 or h>=1<<q or h.bit_count()>P or any(0 in r for r in cs):
        raise ValueError('bad input')
    if P and not q: raise ValueError('empty physical alphabet')
    conflicts=[sum(1<<j for j in range(q) if i!=j and any(-x in cs[j] for x in row))
               for i,row in enumerate(cs)]
    certs=tuple(bicliques)
    for a,b in certs:
        if min(a,b)<=0 or (a|b)>=1<<q or a&b or any(
            a>>i&1 and conflicts[i]&b!=b for i in range(q)): raise ValueError('invalid biclique')
    metrics=dict(work=0,old=0,pins=0,fallback=0,biclique=0,edges=0)
    old={}
    pins={}
    scores={}
    def pay():
        if metrics['work']>=work_cap: raise Missing
        metrics['work']+=1
    def get(c):
        if c not in old:
            pay()
            metrics['old']+=1
            old[c]=old_score(c)
        if old[c] is None: raise Missing
        return old[c]
    def pinned(c,base):
        if pin_count is None: raise Missing
        total=0
        sub=c
        while True:
            pay()
            lits=frozenset(-x for j in range(q) if sub>>j&1 for x in cs[j])
            if not any(-x in lits for x in lits):
                if not lits: val=base
                else:
                    if lits not in pins:
                        metrics['pins']+=1
                        pins[lits]=pin_count(tuple(sorted(lits)))
                    val=pins[lits]
                    if val is None: raise Missing
                total+=(-2)**sub.bit_count()*val
            if not sub: break
            sub=(sub-1)&c
        return total
    def expand(c,base):
        levels=[Counter() for _ in range(c.bit_count()+1)]
        levels[-1][c]=1
        result=0
        for terms in reversed(levels):
            for s,z in terms.items():
                if not z: continue
                pay()
                if s.bit_count()<=P:
                    result+=z*(2*get(s)-base)
                    continue
                cut=None
                for x,y in certs:
                    a,b=x&s,y&s
                    if a and b:
                        cut=a,b
                        metrics['biclique']+=1
                        break
                if cut is None:
                    for i in range(q):
                        b=conflicts[i]&s
                        if s>>i&1 and b:
                            cut=1<<i,b
                            metrics['edges']+=1
                            break
                if cut is None: result+=z*pinned(s,base)
                else:
                    a,b=cut
                    for leaf,coeff in ((s^a,z),(s^b,z),(s^a^b,-z)):
                        levels[leaf.bit_count()][leaf]+=coeff
        return result
    best=None
    for k in range(min(q,P)+1):
        for support in combinations(range(q),k):
            if row_cap is not None and len(scores)>=row_cap:
                return dict(status='cap',metrics=metrics)
            c=sum(1<<i for i in support)
            try:
                base=get(0)
                value,rem=divmod(2*get(h)+2*get(c)-base+expand(c^h,base),4)
                if rem: raise ValueError('inconsistent old scores')
            except Missing:
                if next_score is None: return dict(status='unresolved',metrics=metrics)
                metrics['fallback']+=1
                value=next_score(c)
                if value is None: return dict(status='unresolved',metrics=metrics)
            scores[c]=value
            key=value,k,support
            if best is None or key<best: best=key
    value,k,indices=best
    return dict(status='exact',best=sum(1<<i for i in indices),padding=P-k,
                support=indices,score=value,scores=scores,metrics=metrics)

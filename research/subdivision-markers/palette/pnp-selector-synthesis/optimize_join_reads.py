"""Minimum-rank first read for sparse links modulo dense disabling equations."""
from restricted_join import RowSpan, dot


def optimize(n,links):
    dense=[]
    singleton=[]
    for i,(u,v,tags) in enumerate(links):
        tags=set(tags)
        if not (0<=u<n and 0<=v<n and u!=v and tags<=set(range(4))):
            raise ValueError("invalid link")
        if len(tags)==4:
            return None
        forms=[(f<<(1+2*u))^(f<<(1+2*v)) for f in (1,2,3)]
        if len(tags)==1:
            singleton.append((i,forms))
        elif tags:
            for f,x in enumerate(forms,1):
                values={dot(f,t) for t in set(range(4))-tags}
                if len(values)==1:
                    dense.append(x^values.pop())
    if RowSpan(dense).reduce(1)[0]==0:
        return None
    quotient=RowSpan([1,*dense])
    for _,forms in singleton:
        for i,x in enumerate(forms):
            for p in sorted(quotient.rows,reverse=True):
                if x>>p&1:
                    x^=quotient.rows[p][0]
            forms[i]=x

    def search(space,left):
        choice={}
        for link,forms in singleton:
            for f,x in enumerate(forms,1):
                if space.reduce(x)[0]==0:
                    choice[link]=f
                    break
            else:
                if left:
                    for x in forms:
                        bigger=RowSpan()
                        bigger.rows=space.rows.copy()
                        bigger.add(x,0)
                        answer=search(bigger,left-1)
                        if answer is not None:
                            return answer
                return None
        return choice
    for k in range(len(singleton)+1):
        result=search(RowSpan(),k)
        if result is not None:
            return k,result
    raise AssertionError("unreachable")


def recognize_optimized(n,links):
    """Return the minimum rank, an actual countercolor, or an evaluable link-parity proof."""
    from restricted_join import recognize
    links=[(u,v,tuple(tags)) for u,v,tags in links]
    result=optimize(n,links)
    if result is None:
        return recognize(n,links)
    rank,first_bits=result
    measured,bad,select=recognize(n,links,first_bits)
    if measured != rank:
        raise AssertionError("read rank mismatch")
    return rank,bad,select

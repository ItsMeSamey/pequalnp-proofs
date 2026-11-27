"""Shared exact backend for projected and original CNFs, with charged witness pin queries."""
from affine_mst_complete import compile,enumerate_count
from signed_cover_projection import sat

def solve(n,clauses,*,scope_cap,table_cap,observable_ids=None,backend=None):
    """backend(d, immutable signed CNF) -> nonnegative exact count or (count,witness).
    None or NotImplemented declines this invocation. A positive count without witness
    triggers at most d count calls on successively pinned versions of that same CNF.
    Runtime includes all backend calls. A backend decline on original raises RuntimeError.
    """
    backend=enumerate_count if backend is None else backend
    raw=tuple(tuple(c) for c in clauses)
    calls=[]
    attempts=[]
    def ask(d,cs,route,pins):
        inp=cs+tuple((x,) for x in pins)
        calls.append((route,d,len(inp),len(pins)))
        answer=backend(d,inp)
        if answer is None or answer is NotImplemented: return None
        count,w=answer if isinstance(answer,tuple) else (answer,None)
        if not isinstance(count,int) or not 0<=count<=1<<d: raise ValueError('invalid count')
        if w is not None and (not count or not isinstance(w,int) or not 0<=w<1<<d or
                              not all(sat(c,w) for c in inp)): raise ValueError('invalid witness')
        return count,w
    def counted(d,cs,route):
        ans=ask(d,cs,route,())
        if ans is None or not ans[0] or ans[1] is not None: return ans
        total=left=ans[0]
        pins=[]
        w=0
        for j in range(d):
            test=ask(d,cs,route,(*pins,-(j+1)))
            if test is None: return None
            if test[0]>left: raise ValueError('inconsistent pinned count')
            if test[0]:
                if test[1] is not None: return total,test[1]
                pins.append(-(j+1))
                left=test[0]
            else:
                pins.append(j+1)
                w|=1<<j
        if left!=1 or not all(sat(c,w) for c in cs): raise ValueError('count-only recovery failed')
        return total,w
    charts=[('automatic',None)]
    if observable_ids is not None: charts.insert(0,('supplied',tuple(observable_ids)))
    for route,ids in charts:
        chart=compile(n,raw,scope_cap=scope_cap,table_cap=table_cap,observable_ids=ids)
        if chart is None:
            attempts.append((route,'invalid-or-cap'))
            continue
        ans=(0,None) if not chart.fiber else counted(len(chart.tree),chart.clauses,route)
        if ans is None:
            attempts.append((route,'backend-declined'))
            continue
        count,w=ans
        return dict(count=count*chart.fiber,witness=None if w is None else chart.lift(w),
                    route=route,calls=calls,attempts=attempts+[(route,'accepted')])
    ans=counted(n,raw,'original')
    if ans is None: raise RuntimeError('shared backend declined original or required pin query')
    return dict(count=ans[0],witness=ans[1],route='original',calls=calls,attempts=attempts)

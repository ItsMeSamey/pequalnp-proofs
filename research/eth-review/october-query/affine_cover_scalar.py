"""Exact prefix and trial scores on signed CNFs via a primal vertex cover."""
def score(n,clauses,rows,trial=0,*,cover=None,pins=(),assignment_cap):
    """Signed one-based pins and literals. Parity masks use physical row order."""
    if n<0 or assignment_cap<0: raise ValueError('invalid cap or dimension')
    cs=[]
    for row in clauses:
        literals=frozenset(row)
        if any(not 1<=abs(x)<=n for x in literals): raise ValueError('invalid literal')
        cs.append(None if any(-x in literals for x in literals) else literals)
    rows=tuple(rows)
    if any(not 0<=h<1<<len(cs) for h in (*rows,trial)): raise ValueError('bad mask')
    fixed={}
    inconsistent=False
    for lit in pins:
        if not 1<=abs(lit)<=n: raise ValueError('bad pin')
        if abs(lit) in fixed and fixed[abs(lit)]!=(lit>0): inconsistent=True
        fixed[abs(lit)]=int(lit>0)
    if inconsistent: return dict(status='exact',prefix=0,score=0,assignments=0,cover=())
    active=[None if row is None or any(fixed.get(abs(x))==(x>0) for x in row)
            else tuple(sorted(x for x in row if abs(x) not in fixed)) for row in cs]
    if cover is None:
        chosen=set()
        for row in active:
            if row is None: continue
            unmatched=[abs(x) for x in row if abs(x) not in chosen]
            for j in range(0,len(unmatched)-1,2):
                chosen.update(unmatched[j:j+2])
    else:
        chosen=set(cover)
        if any(not 1<=x<=n for x in chosen): raise ValueError('bad cover variable')
        chosen-=fixed.keys()
    if any(row is not None and sum(abs(x) not in chosen for x in row)>1 for row in active):
        raise ValueError('supplied set misses a primal edge')
    chosen=tuple(sorted(chosen))
    num=1<<len(chosen)
    if num>assignment_cap: return dict(status='budget',required=num,cover=chosen)
    count=answer=0
    free=n-len(fixed)-len(chosen)
    for v in range(num):
        a={x:v>>j&1 for j,x in enumerate(chosen)}
        forms=[]
        for row in active:
            if row is None or any(a.get(abs(x))==(x>0) for x in row):
                forms.append(0)
                continue
            last=next((x for x in row if abs(x) not in a),0)
            forms.append((1<<abs(last)) ^ int(last>0) if last else 1)
        piv={}
        def add(mask):
            eq=0
            while mask:
                bit=mask&-mask
                eq^=forms[bit.bit_length()-1]
                mask^=bit
            while eq>1:
                i=eq.bit_length()-1
                if i not in piv:
                    piv[i]=eq
                    return True
                eq^=piv[i]
            return not eq
        if all(add(h) for h in rows):
            count+=1<<(free-len(piv))
            if add(trial): answer+=1<<(free-len(piv))
    return dict(status='exact',prefix=count,score=answer,cover=chosen,assignments=num)

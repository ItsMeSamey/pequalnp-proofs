"""Check all restricted singleton and split witnesses used in the large-signature proof."""
from collections import Counter
from itertools import combinations
from samples import neg,lines

def flags(ns,cut,allowed):
    active=[i for i in range(13) if not (cut>>i&1)]
    assert all(T&~cut for T in lines)
    assert all(any(q>>p&1 for q,l in ns) for p in active)
    # A zero-line rejected point set witnessing an attempted AND split.
    assert all(any(q&A&~cut and q&B&~cut for q,l in ns) for A,B in combinations(lines,2))
    for j,T in enumerate(lines):
        for k,U in enumerate(lines):
            if j==k or not allowed(j,k):continue
            for p in active:
                if T>>p&1:continue
                assert any(l>>j&1 and q>>p&1 and q&U&~cut for q,l in ns), (j,k,p)

def badpoints(ns,targets,cut=0):
    return {p for p in range(13) if not cut>>p&1
            and not any(q>>p&1 and any(q&U&~cut for U in targets) for q,l in ns)}

def check():
    out=Counter()
    for s in range(3,8):
        for I in combinations(range(7),s):
            mask=sum(1<<i for i in I)
            ns=[(q,l) for q,l in neg if l&mask]
            concurrent=bool(lines[I[0]]&lines[I[1]]&lines[I[2]]) if s==3 else False
            if s>=4 or concurrent:
                missing=set().union(*(badpoints(ns,[U]) for U in lines))
                # Also remove any globally uncovered singleton and any outside
                # singleton lacking its required T-active, U-meeting extension.
                for p in range(13):
                    for j,T in enumerate(lines):
                        if T>>p&1:continue
                        if any(not any(l>>j&1 and q>>p&1 and q&U for q,l in ns)
                               for k,U in enumerate(lines) if k!=j):missing.add(p)
                assert len(missing)<=1
                cut=sum(1<<p for p in missing)
                assert sum((T&cut).bit_count() for T in lines)<=3
                flags(ns,cut,lambda j,k:True)
                assert all(not badpoints(ns,[U],cut) for U in lines)
                out[s,'full',len(missing)]+=1
            else:
                directional=lambda j,k:j in I or k not in I
                flags(ns,0,directional)
                # With two resident lines the pinned exterior never loses its
                # zero-line rejection at any singleton.
                assert all(not badpoints(ns,[A,B]) for A,B in combinations(lines,2))
                for j,D in enumerate(lines):
                    missing=badpoints(ns,[D])
                    assert len(missing)<=1 and (j in I or not missing)
                    cut=sum(1<<p for p in missing)
                    assert sum((T&cut).bit_count() for T in lines)<=3
                    flags(ns,cut,directional)
                    assert not badpoints(ns,[D],cut)
                out[s,'directional',0]+=1
    print(dict(sorted(out.items())))
if __name__=='__main__':check()

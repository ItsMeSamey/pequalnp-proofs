"""Arbitrary alternating query for indexed cographic hosts with a supplied chordal order."""
from itertools import permutations
from planar_moment_certificate import CertifiedDual


def product(left,right):
    out=set()
    for a,b in left:
        for c,d in right:
            x=a|c;y=b|d
            if not x&y: out.symmetric_difference_update(((x,y),))
    return out


def query(n, edges, order, entries):
    """entries gives the nonzero (i,j), i<j, of the queried original-site form."""
    dual=CertifiedDual(n,tuple(tuple(edge) for edge in edges)); order=tuple(order)
    if set(order)!=set(range(n)) or len(order)!=n: raise ValueError("invalid order")
    pos={v:i for i,v in enumerate(order)}
    neighbors=[{w for w,_ in ring if w!=v} for v,ring in enumerate(dual.graph)]
    later={v:sorted(w for w in neighbors[v] if pos[w]>pos[v]) for v in order}
    if any(any(z not in neighbors[w] for z in later[v] if z!=w) for v in order for w in later[v]):
        raise ValueError("not a perfect elimination order")
    form=set()
    for i,j in entries:
        if not 0<=i<j<len(dual.edges):raise ValueError("invalid exterior coordinate")
        for p,q in ((i,j),(j,i)):
            for u in dual.edges[p][:2]:
                for v in dual.edges[q][:2]:
                    if u!=v:form.symmetric_difference_update(((1<<u,1<<v),))
    for color in (0,1):
        for bit in (1,2):
            factor={(0,0)}
            for v,charge in enumerate(dual.charge):
                if bit&charge:
                    factor.add(((1<<v,0) if color==0 else (0,1<<v)))
            form=product(form,factor)
    if not form:return None
    # Encode at most six demands as a basis coordinate, allocated only when reached.
    ids={};terms=[]
    def encode(polynomial):
        mask=0
        for term in polynomial:
            i=ids.get(term)
            if i is None:
                i=len(terms);ids[term]=i;terms.append(term)
            mask^=1<<i
        return mask
    initial=encode(form); final=encode(((0,0),))
    for roots in permutations(order,3):
        if any(not later[v] and v not in roots for v in order):continue
        layer=[(initial,())]
        for v in order:
            pivots={}; next_layer=[]; vb=1<<v
            options=(None,) if v in roots else later[v]
            for w in options:
                cache={}
                for vector,path in layer:
                    value=0;scan=vector
                    while scan:
                        low=scan&-scan;scan^=low;i=low.bit_length()-1
                        if i not in cache:
                            a,b=terms[i];at_a=bool(a&vb);at_b=bool(b&vb)
                            a&=~vb;b&=~vb
                            if w is None:
                                valid=(not at_a or v==roots[0]) and (not at_b or v==roots[2])
                            else:
                                if at_a:a|=1<<w
                                if at_b:b|=1<<w
                                valid=not a&b
                            cache[i]=encode(((a,b),)) if valid else 0
                        value^=cache[i]
                    reduced=value
                    while reduced:
                        p=reduced.bit_length()-1
                        if p not in pivots:
                            pivots[p]=reduced
                            next_layer.append((value,path+(w,)))
                            break
                        reduced^=pivots[p]
            layer=next_layer
            if not layer:break
        if layer:
            vector,parents=layer[0]
            if vector!=final:raise AssertionError("residual demand")
            assignment={}
            for v,w in reversed(list(zip(order,parents))):
                assignment[v]=roots.index(v) if w is None else assignment[w]
            sets=[sum(1<<v for v in order if assignment[v]==i) for i in range(3)]
            left,right=sets[0],sets[2]
            if not dual.compatible(left,right):raise AssertionError("incompatible cuts")
            return dual.cut(left),dual.cut(right),sets
    return None


def basis(n,edges,order):
    """Recover a physical witness basis by keeping the current annihilator."""
    edges=tuple(tuple(edge) for edge in edges);order=tuple(order)
    coords=[(i,j) for i in range(len(edges)) for j in range(i+1,len(edges))]
    forms=[1<<s for s in range(len(coords))]
    def entries(mask):
        while mask:
            bit=mask&-mask;mask^=bit
            yield coords[bit.bit_length()-1]
    while forms:
        omega=forms.pop()
        answer=query(n,edges,order,entries(omega))
        if answer is None:continue
        a,b,parts=answer
        word=sum(((((a>>i)&(b>>j))^((a>>j)&(b>>i)))&1)<<s for s,(i,j) in enumerate(coords))
        if not (omega&word).bit_count()%2:raise AssertionError("invalid separator witness")
        forms=[f^omega if (f&word).bit_count()%2 else f for f in forms]
        yield a,b,parts

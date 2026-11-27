"""Produce parity certificates of universal crossing-link availability."""


def certificate(n, links):
    """Links store endpoint indices and available tag sets. Terms encode scalar violations."""
    rows = {}
    terms = []
    for i,(u,v,tags) in enumerate(links):
        tags=set(tags)
        if not (0<=u<n and 0<=v<n and u!=v and tags<=set(range(4))):
            raise ValueError("bad cross-link")
        missing=set(range(4))-tags
        if not missing:
            return [(i,0,1)]
        for f in (1,2,3):
            values={(f&t).bit_count()%2 for t in missing}
            if len(values)!=1:
                continue
            rhs=values.pop()
            x=(f<<(2*u))^(f<<(2*v))
            witness=1<<len(terms)
            terms.append((i,f,rhs))
            while x:
                p=x.bit_length()-1
                if p not in rows:
                    rows[p]=(x,rhs,witness)
                    break
                y,b,z=rows[p]
                x^=y
                rhs^=b
                witness^=z
            else:
                if rhs:
                    return [term for j,term in enumerate(terms) if witness>>j&1]
    return None


def active_selection(links, proof, colors):
    result=set()
    for i,f,b in proof:
        u,v,tags=links[i]
        tag=colors[u]^colors[v]
        if ((f&tag).bit_count()%2)^b:
            if tag not in tags:
                raise ValueError("inactive link selected")
            result.symmetric_difference_update((i,))
    return result

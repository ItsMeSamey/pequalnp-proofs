"""Exact named kernels using at most d+1 colors without guessing their basis."""
from itertools import product
from compact import canonical, image, nullspace, solve


def exact(compression, K):
    """Return an original contraction set, or None for an unattainable named kernel."""
    K=canonical(K)
    B=compression.roots
    if any(v>>len(B) for v in K):
        raise ValueError("unexpected coordinates in the proposed kernel")
    vectors=[solve(compression.U,image(B,z)) for z in K]
    if None in vectors:
        return None
    W=canonical(vectors)
    if len(K)!=len(B)-len(canonical(B))+len(W):
        return None
    reduced=trace(compression.reduced,compression.smallport,compression.reducedtype,W)
    if reduced is None:
        return None
    return compression.transfer(reduced,True)


def trace(block, port, types, W):
    d=len(port)
    r=len(W)
    s=d-r
    if not r:
        return 0
    if not s:
        return (1<<len(block.cols))-1
    colors=s+1
    bits_per_color=s.bit_length()
    dual=canonical(nullspace(W,d))
    demand={v:sum(((h&w).bit_count()%2)<<j for j,w in enumerate(W)) for v,(_,h) in types.items()}
    options=[[m for m in range(1,1<<colors) if m.bit_count()<=len(p)] for p in block.parts]
    for pattern in product(*options):
        comp=block.component_bits(pattern,colors)
        occupancy=sum(mask<<(colors*i) for i,mask in enumerate(pattern))
        table={(0,0):0}
        for i,part in enumerate(block.parts):
            for v in part:
                new={}
                for a in range(colors):
                    if not pattern[i]>>a&1:
                        continue
                    j=comp[i,a]
                    if j is None and demand[v]:
                        continue
                    add=0 if not a else types[v][1]<<(d*(a-1))
                    if j is not None:
                        add |= demand[v]<<(d*s+r*j)
                    mark=1<<(colors*i+a)
                    for (state,seen),old in table.items():
                        new.setdefault((state^add,seen|mark),old|(a<<(bits_per_color*v)))
                table=new
        for (state,seen),assignment in table.items():
            if seen!=occupancy or state>>(d*s):
                continue
            h=canonical((state>>(d*i))&((1<<d)-1) for i in range(s))
            if h!=dual:
                continue
            color=[(assignment>>(bits_per_color*v))&((1<<bits_per_color)-1) for v in range(block.n)]
            allowed=[i for i,(v,w) in enumerate(block.edges) if color[v]==color[w]]
            cols=tuple(block.cols[i] for i in allowed)
            mask=0
            for z in W:
                select=solve(cols,image(port,z))
                assert select is not None
                mask |= sum(1<<i for j,i in enumerate(allowed) if select>>j&1)
            return mask
    return None

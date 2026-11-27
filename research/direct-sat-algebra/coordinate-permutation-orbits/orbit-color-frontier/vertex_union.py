"""Vertex-ordered forbidden-neighborhood union DP on a canonical four-color orbit."""
from itertools import combinations
from math import isqrt
from cycle_syndrome import _word,apply_word,build


def solve(raw,vertex_order=None):
    """Return an original generator word or None. Order includes any padding vertex."""
    D=len(raw.rotation)
    n=(1+isqrt(1+2*D))//2
    if n%2!=1 or D!=2*n*(n-1):
        raise ValueError("unrecognized canonical orbit size")
    ref=build(n,[])
    if (tuple(raw.rotation),tuple(raw.flip),raw.start)!=(ref.rotation,ref.flip,ref.start):
        raise ValueError("unrecognized canonical orbit")
    if type(raw.zero)!=int or raw.zero<0 or raw.zero.bit_length()>D:
        raise ValueError("invalid zero pins")
    order=list(range(n)) if vertex_order is None else list(vertex_order)
    if len(order)!=n or any(type(v)!=int for v in order) or set(order)!=set(range(n)):
        raise ValueError("order must permute the physical vertices")
    rows=[[0]*4 for _ in range(n)]
    for i,(u,v) in enumerate(combinations(range(n),2)):
        mask=raw.zero>>(4*i)
        for delta in range(4):
            if mask>>delta&1:
                rows[u][delta]|=1<<v
                rows[v][delta]|=1<<u
    empty=(0,0,0,0)
    layers=[{empty:None}]
    future=(1<<n)-1
    for i,v in enumerate(order):
        future^=1<<v
        layer={}
        for bans in layers[-1]:
            # Global color translation preserves every endpoint difference.
            for c in range(4 if i else 1):
                if bans[c]>>v&1:continue
                successor=tuple((bans[b]|rows[v][c^b])&future for b in range(4))
                layer.setdefault(successor,(bans,c))
        if not layer:return None
        layers.append(layer)
    colors=[0]*n
    key=empty
    for i in reversed(range(n)):
        key,colors[order[i]]=layers[i+1][key]
    word=_word(n,colors)
    physical=apply_word(raw,word)
    expected=sum(1<<(4*i+(colors[u]^colors[v])) for i,(u,v) in enumerate(combinations(range(n),2)))
    if physical!=expected or physical&raw.zero:raise ArithmeticError("raw replay failed")
    return word

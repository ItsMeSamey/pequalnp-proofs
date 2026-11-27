"""Exact edge-list trellis for canonical four-position raw translation orbits."""
from itertools import combinations
from math import isqrt
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"binary-modular-bases"))
from four_color_orbit import build
from orbit_subcube import apply_word


def _reduce(v,basis):
    for pivot in sorted(basis,reverse=True):
        if v>>pivot&1:v^=basis[pivot]
    return v


def _insert(v,basis):
    v=_reduce(v,basis)
    if v:basis[v.bit_length()-1]=v


def _cycles(n,edges):
    forest=[[] for _ in range(n)]
    cols=[0]*len(edges)
    chords=0
    for i,(u,v) in enumerate(edges):
        prev={u:None}
        todo=[u]
        while todo and v not in prev:
            x=todo.pop()
            for z,j in forest[x]:
                if z not in prev:
                    prev[z]=(x,j)
                    todo.append(z)
        if v not in prev:
            forest[u].append((v,i))
            forest[v].append((u,i))
        else:
            flag=1<<chords
            chords+=1
            cols[i]|=flag
            x=v
            while x!=u:
                x,j=prev[x]
                cols[j]|=flag
    return cols,forest


def _word(n,colors):
    pieces=[]
    for v,c in enumerate(colors):
        for b in (0,1):
            if c>>b&1:
                s=v if v%2==b else v+n
                pieces.extend(('r'*((-s)%(2*n)),'f','r'*s))
    return ''.join(pieces)


def solve(raw,edge_order=None):
    """Return an accepted raw word, or None for UNSAT. Reject unrecognized layouts.

    Edge order uses unordered pairs of physical vertex indices. It must contain
    every constrained edge once; optional unconstrained edges are dropped.
    """
    D=len(raw.rotation)
    n=(1+isqrt(1+2*D))//2
    if n%2!=1 or D!=2*n*(n-1):
        raise ValueError("unrecognized canonical orbit size")
    ref=build(n,[])
    if (tuple(raw.rotation),tuple(raw.flip),raw.start)!=(ref.rotation,ref.flip,ref.start):
        raise ValueError("unrecognized canonical orbit")
    if type(raw.zero)!=int or raw.zero<0 or raw.zero.bit_length()>D:
        raise ValueError("invalid zero pins")
    allowed={}
    for i,e in enumerate(combinations(range(n),2)):
        mask=15^(raw.zero>>(4*i)&15)
        if mask!=15:allowed[e]=mask
    if edge_order is None:
        edges=list(allowed)
    else:
        order=[tuple(sorted(e)) for e in edge_order]
        if (any(len(e)!=2 or any(type(x)!=int or not 0<=x<n for x in e)
                or e[0]==e[1] for e in order)
                or len(set(order))!=len(order) or not allowed.keys()<=set(order)):
            raise ValueError("invalid edge order")
        edges=[e for e in order if e in allowed]
    cols,forest=_cycles(n,edges)
    suffix=[{} for _ in range(len(edges)+1)]
    for i in reversed(range(len(edges))):
        suffix[i]=dict(suffix[i+1])
        _insert(cols[i],suffix[i])
    layers=[{(0,0):None}]
    for i,e in enumerate(edges):
        layer={}
        for state in layers[-1]:
            for color in range(4):
                if not (allowed[e]>>color)&1:continue
                a=state[0]^(cols[i] if color&1 else 0)
                b=state[1]^(cols[i] if color&2 else 0)
                if _reduce(a,suffix[i+1]) or _reduce(b,suffix[i+1]):continue
                layer.setdefault((a,b),(state,color))
        if not layer:return None
        layers.append(layer)
    deltas=[0]*len(edges)
    state=(0,0)
    for i in reversed(range(len(edges))):
        state,deltas[i]=layers[i+1][state]
    colors=[None]*n
    for root in range(n):
        if colors[root] is not None:continue
        colors[root]=0
        todo=[root]
        while todo:
            x=todo.pop()
            for y,j in forest[x]:
                if colors[y] is None:
                    colors[y]=colors[x]^deltas[j]
                    todo.append(y)
    if any(colors[x]^colors[y]!=t for (x,y),t in zip(edges,deltas)):
        raise ArithmeticError("forest integration failed")
    word=_word(n,colors)
    physical=apply_word(raw,word)
    expected=sum(1<<(4*i+(colors[x]^colors[y])) for i,(x,y) in enumerate(combinations(range(n),2)))
    if physical!=expected or physical&raw.zero:
        raise ArithmeticError("original orbit replay failed")
    return word

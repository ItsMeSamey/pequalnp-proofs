"""Minimize a sum of signed affine-cell functions using a supplied binary leaf tree."""
from dataclasses import dataclass, field
from fractions import Fraction
from affine_cell_energy import AffineCellEnergy, dot, solve
from affine_edge_cache import AffineEdgeCache
from affine_syndrome_trellis import minimum_table


def _basis(forms):
    selected = []
    pivots = {}
    for a in forms:
        reduced = a
        while reduced:
            k = reduced.bit_length()-1
            if k not in pivots:
                pivots[k] = reduced
                selected.append(a)
                break
            reduced ^= pivots[k]
    return tuple(selected)


def _orth(d, forms):
    return solve(d, ((a,0) for a in forms))[1]


def _intersect(d, left, right):
    return _orth(d,_orth(d,left)+_orth(d,right))


def _eval(forms,point):
    return sum(dot(a,point)<<i for i,a in enumerate(forms))


def _combine(directions,word):
    result = 0
    for i,a in enumerate(directions):
        if word>>i&1:
            result ^= a
    return result


def _section(d,basis):
    """Map prescribed basis evaluations to one vector realizing them."""
    return tuple(solve(d,((a,int(i==j)) for j,a in enumerate(basis)))[0]
                 for i in range(len(basis)))


def _pull(terms,base,directions):
    return [(w,[(_eval(directions,a), b^dot(a,base)) for a,b in rows])
            for w,rows in terms]


class SpectrumLimit(ValueError):
    """The leaf has more nonzero Walsh coefficients than requested."""


def sparse_spectrum(d,terms,cap,energy=None):
    """Normalized signed Walsh coefficients, or None if support exceeds cap."""
    if not isinstance(cap,int) or cap<0:
        raise ValueError("invalid support cap")
    energy = AffineCellEnergy(d,terms) if energy is None else energy
    records=[]
    for weight,rows in terms:
        cell=solve(d,rows)
        if cell is not None and weight:
            point,kernel=cell
            records.append((Fraction(weight,1 << (d-len(kernel))),point,kernel))
    out={}
    stack=[(0,0,())]
    while stack:
        i,mask,filters=stack.pop()
        if not energy.energy(filters):
            continue
        if i==d:
            if len(out)==cap:
                return None
            coeff=sum(-w if dot(mask,p) else w for w,p,ker in records
                      if all(not dot(mask,k) for k in ker))
            assert coeff
            out[mask]=coeff
            continue
        bit=1<<i
        stack.append((i+1,mask|bit,filters+((bit,1),)))
        stack.append((i+1,mask,filters+((bit,0),)))
    return out


@dataclass
class _Node:
    span: tuple
    index: int = -1
    children: tuple = ()
    boundary: tuple = ()
    leaf_basis: tuple = ()
    table: dict = field(default_factory=dict)


def minimize(n, leaves, tree, equations=(), *, leaf_strategy="auto", spectrum_cap=None):
    """Return (minimum, original assignment mask), or None on infeasible equations.

    leaves[i] is a sequence of (rational weight, affine cell equations).
    tree is a leaf index or a pair of child trees, and must use each index once.
    For no leaves use None. Equations have (little-endian mask, binary rhs) form.
    """
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid dimension")
    if leaf_strategy not in ("auto","edge","sparse-edge","trellis"):
        raise ValueError("invalid leaf strategy")
    if spectrum_cap is not None and (not isinstance(spectrum_cap,int) or spectrum_cap<0):
        raise ValueError("invalid spectrum cap")
    domain = solve(n,equations)
    if domain is None:
        return None
    base, directions = domain
    d = len(directions)
    inputs = []
    for leaf in leaves:
        terms = []
        for w,cell in leaf:
            rows = tuple(cell)
            if any(not isinstance(a,int) or not 0<=a<1<<n or b not in (0,1) for a,b in rows):
                raise ValueError("invalid cell equation")
            terms.append((w,rows))
        inputs.append(_pull(terms,base,directions))
    if not inputs and tree is None:
        return 0,base
    spectra=[]
    interfaces=[]
    for terms in inputs:
        energy=AffineCellEnergy(d,terms)
        spectrum=None
        if leaf_strategy!="edge":
            spectrum=sparse_spectrum(d,terms,d+1 if spectrum_cap is None else spectrum_cap,energy)
            if spectrum is None and leaf_strategy in ("sparse-edge","trellis"):
                raise SpectrumLimit("leaf support exceeds cap")
        spectra.append(spectrum)
        interfaces.append(_basis(spectrum) if spectrum is not None else energy.interface())
    seen=set()
    def build(t):
        if isinstance(t,int):
            if not 0<=t<len(inputs) or t in seen:
                raise ValueError("invalid or repeated leaf")
            seen.add(t)
            return _Node(interfaces[t],index=t)
        if not isinstance(t,(tuple,list)) or len(t)!=2:
            raise ValueError("expected binary subtree")
        l,r = map(build,t)
        return _Node(_basis(l.span+r.span),children=(l,r))
    root=build(tree)
    if len(seen)!=len(inputs):
        raise ValueError("tree omits a leaf")

    def populate(node,outside):
        W=node.boundary=_intersect(d,node.span,outside)
        if not node.children:
            B=node.leaf_basis=_basis(W+node.span)
            spectrum=spectra[node.index]
            if spectrum is not None and leaf_strategy in ("auto","trellis"):
                terms=[(w,mask,0) for mask,w in spectrum.items()]
                minima,_=minimum_table(d,terms,[(a,0) for a in W])
                node.table={beta:(cost,_eval(B,x)) for beta,(cost,x) in minima.items()}
                return
            section=_section(d,B)
            for beta in range(1<<len(W)):
                start=_combine(section,beta)
                terms=_pull(inputs[node.index],start,section[len(W):])
                cache=AffineEdgeCache(len(B)-len(W),terms)
                value,suffix=cache.extrema()[0]
                node.table[beta]=(value,beta|(suffix<<len(W)))
            return
        l,r=node.children
        populate(l,_basis(outside+r.span))
        populate(r,_basis(outside+l.span))
        J=_basis(l.boundary+r.boundary)
        if len(_basis(J+W)) != len(J):
            raise AssertionError("parent boundary outside child boundary sum")
        section=_section(d,J)
        for z in range(1<<len(J)):
            point=_combine(section,z)
            a,b,beta=(_eval(space,point) for space in (l.boundary,r.boundary,W))
            cost=l.table[a][0]+r.table[b][0]
            if beta not in node.table or cost<node.table[beta][0]:
                node.table[beta]=(cost,(a,b))
    populate(root,())

    chosen=[]
    def backtrack(node,key):
        _,step=node.table[key]
        if node.children:
            for child,child_key in zip(node.children,step):
                backtrack(child,child_key)
        else:
            chosen.extend((a,(step>>i)&1) for i,a in enumerate(node.leaf_basis))
    backtrack(root,0)
    realizer=solve(d,chosen)
    if realizer is None:
        raise AssertionError("incompatible traceback")
    return root.table[0][0],base^_combine(directions,realizer[0])

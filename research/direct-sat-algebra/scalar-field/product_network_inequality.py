"""One raw Boolean quadratic condition on a translated field-product network."""
from dataclasses import dataclass
from binomial_inequation import nonzero
from quadratic_image import normalize, parity
from quadratic_target import apply_basis, insert, interpolate, reduce_vector


@dataclass(frozen=True)
class Instance:
    arity: int
    equations: tuple
    polynomial: tuple


def trace_dual(field):
    """Compute the trace-dual polynomial basis by binary elimination."""
    m = field.m
    pivots = {}
    for i in range(m):
        functional = sum(field.trace(field.mul(1<<i,1<<j)) << j for j in range(m))
        if not insert(functional,1<<i,pivots):
            raise ValueError("singular field trace form")
    return [reduce_vector(1<<k,pivots)[1] for k in range(m)]


def compile_instance(field, frames, shift, edges, output_offset, target, form, required=1):
    """Edges encode z_i*z_j^(2^twist); each basis is a tuple of packed columns."""
    frames = [tuple(fr) for fr in frames]
    edges = list(edges)
    m, arity = field.m, len(frames)
    n = m*arity
    if required not in (0,1) or not 0 <= shift < 1<<n or min(output_offset,target)<0:
        raise ValueError("invalid translation, target or desired bit")
    columns = [v for fr in frames for v in fr]
    if any(len(fr)!=m for fr in frames):
        raise ValueError("invalid input frame width")
    pivots = {}
    if any(not 0<v<1<<n or not insert(v,1<<k,pivots) for k,v in enumerate(columns)):
        raise ValueError("input columns must be a full binary basis")
    pivots = {}
    for e,(i,j,t,basis) in enumerate(edges):
        if not (0<=i<arity and 0<=j<arity and isinstance(t,int) and len(basis)==m):
            raise ValueError("invalid product edge")
        for k,v in enumerate(basis):
            if v<=0 or not insert(v,1<<(m*e+k),pivots):
                raise ValueError("output columns must be independent")
    c, lin, pairs = normalize(n,form)
    residue, goal = reduce_vector(target ^ output_offset,pivots)
    if residue:
        return None
    zeros = (0,)*arity
    equations = []
    for e,(i,j,t,_) in enumerate(edges):
        ex = [0]*arity
        ex[i] += 1
        ex[j] += 1 << (t%m)
        equations.append(((1,tuple(ex)),((goal >> (e*m)) % field.size,zeros)))

    def raw_value(y):
        x = shift ^ apply_basis(columns,y)
        quadratic = sum((x>>i)&(x>>j)&1 for i,j in pairs)
        return c ^ parity(lin & x) ^ (quadratic & 1) ^ 1 ^ required

    base, linear, quadratic = interpolate(raw_value,n)
    expansion = {zeros:1} if base else {}
    dual = trace_dual(field)
    traces = []
    for i in range(n):
        alpha = dual[i%m]
        terms = []
        for h in range(m):
            ex = [0]*arity
            ex[i//m] = 1<<h
            terms.append((alpha,tuple(ex)))
            alpha = field.mul(alpha,alpha)
        traces.append(terms)

    def accumulate(ex,coefficient):
        expansion[ex] = expansion.get(ex,0) ^ coefficient
        if not expansion[ex]:
            del expansion[ex]

    for i,active in enumerate(linear):
        if active:
            for a,ex in traces[i]:
                accumulate(ex,a)
    order = field.size-1
    for i,j in quadratic:
        for a,ex in traces[i]:
            for b,ey in traces[j]:
                powers = tuple(1+(u+v-1)%order if u+v else 0 for u,v in zip(ex,ey))
                accumulate(powers,field.mul(a,b))
    return Instance(arity,tuple(equations),tuple((a,ex) for ex,a in expansion.items()))


def decide(field,frames,shift,edges,output_offset,target,form,required=1):
    inst = compile_instance(field,frames,shift,edges,output_offset,target,form,required)
    return inst is not None and nonzero(field,inst.arity,inst.equations,inst.polynomial)

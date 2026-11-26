"""Compile certified selector cliques in rank-at-most-two affine flat avoidance."""
from dataclasses import dataclass
from itertools import combinations
from affine_cover_solver import insert, reduce_equation


def parity(v):
    return v.bit_count() & 1


def solution(basis):
    x = 0
    for p in sorted(basis):
        m,t = basis[p]
        x |= (t ^ parity(m & x)) << p
    return x


def normalize(rows):
    basis = {}
    for m,t in rows:
        if not insert(m,t,basis):
            return None
    return tuple(basis.values())


def reduce_vector(v, pivots):
    label = 0
    while v and v.bit_length()-1 in pivots:
        m,s = pivots[v.bit_length()-1]
        v ^= m
        label ^= s
    return v,label


@dataclass(frozen=True)
class Arm:
    word: int
    selector: int
    equations: tuple


@dataclass(frozen=True)
class SelectorProjection:
    n: int
    rank: int
    frame: tuple
    projections: tuple
    core_flats: tuple
    arms: tuple

    @property
    def core_n(self):
        return self.n-self.rank

    def lift(self, arm, z):
        basis = {}
        for j,m in enumerate(self.frame):
            if j < self.rank:
                bit = arm.selector >> j & 1
            else:
                i = j-self.rank
                bit = (z >> i & 1) ^ parity(self.projections[i] & arm.selector)
            insert(m,bit,basis)
        return solution(basis)

    def one_equation_union(self):
        """Forbidden complement flat, None if the union is whole, () if it is empty."""
        if any(len(a.equations)>1 for a in self.arms):
            raise ValueError("an arm has multiple independent equations")
        if any(not a.equations for a in self.arms):
            return None
        return normalize((m,t^1) for a in self.arms for m,t in a.equations)


def build_projection(n, flats, forms):
    """Return an exact split or None on failed clique/complement certification.

    w_i=parity(mask & x) XOR offset. Each simultaneously feasible selected pair
    must imply one listed forbidden flat. Core dimension includes all free bits.
    """
    if not isinstance(n,int) or n<0:
        raise ValueError("invalid dimension")
    def valid(rows):
        rows=tuple(rows)
        if any(not isinstance(m,int) or m<0 or m.bit_length()>n or t not in (0,1) for m,t in rows):
            raise ValueError("invalid affine equation")
        return rows
    forms=valid(forms)
    clean=[]
    for flat in flats:
        flat=normalize(valid(flat))
        if flat is not None:
            if len(flat)>2:
                raise ValueError("flat rank exceeds two")
            clean.append(flat)
    for (a,t),(b,u) in combinations(forms,2):
        pair={}
        if insert(a,t^1,pair) and insert(b,u^1,pair):
            if not any(all(reduce_equation(m,v,pair)==(0,0) for m,v in flat) for flat in clean):
                return None

    frame=[]; pivots={}
    def extend(v):
        row,label=reduce_vector(v,pivots)
        if row:
            pivots[row.bit_length()-1]=row,label^(1<<len(frame))
            frame.append(v)
    for m,_ in forms:
        extend(m)
    k=len(frame); low=(1<<k)-1
    for i in range(n):
        extend(1<<i)
    def coord(m):
        return reduce_vector(m,pivots)[1]
    forms=tuple((coord(m),t) for m,t in forms)
    constraints={}
    def projected_bit(v,j):
        mask=0
        remaining=v>>k
        while remaining:
            bit=remaining&-remaining
            mask |= 1<<((bit.bit_length()-1)*k+j)
            remaining ^= bit
        return mask,(v>>j)&1

    core=[]; dependent=[]
    for flat in clean:
        rows=tuple((coord(m),t) for m,t in flat)
        if all(not(v>>k) for v,_ in rows):
            dependent.append(rows)
            continue
        span=list(rows)
        if len(rows)==2:
            (a,s),(b,t)=rows
            span.append((a^b,s^t))
        h=next((v for v,_ in span if not(v>>k)),0)
        if not h:
            core.append(tuple((v>>k,t) for v,t in rows))
            required=[(v,0) for v,_ in rows]
        else:
            dependent.append(rows)
            required=[(next(v for v,_ in rows if v>>k),h)]
        for v,h in required:
            lead=h.bit_length()-1
            for j in range(k):
                if j==lead:
                    continue
                m,t=projected_bit(v,j)
                if h>>j&1:
                    other,s=projected_bit(v,lead)
                    m ^= other
                    t ^= s
                if not insert(m,t,constraints):
                    return None

    unknown=solution(constraints)
    projections=tuple((unknown>>(i*k))&low for i in range(n-k))
    def proj(v):
        value=v&low
        for i,p in enumerate(projections):
            if v>>(k+i)&1:
                value ^= p
        return value
    arms=[]
    for word in (0,*(1<<i for i in range(len(forms)))):
        fix={}
        if not all(insert(m,t^((word>>j)&1),fix) for j,(m,t) in enumerate(forms)):
            continue
        y=solution(fix); pins={}
        for flat in dependent:
            residual=normalize((v>>k,t^parity(proj(v)&y)) for v,t in flat)
            if residual is None:
                continue
            if not residual:
                break
            (m,t),=residual
            if not insert(m,t^1,pins):
                break
        else:
            arms.append(Arm(word,y,tuple(pins.values())))
    return SelectorProjection(n,k,tuple(frame),projections,tuple(core),tuple(arms))

"""Exact semantic affine-edge ordered cache for signed rational mixtures of cells."""
from dataclasses import dataclass
from fractions import Fraction
from affine_cover_solver import insert


def _basis(rows):
    basis={}
    for a,b in rows:
        if not insert(a,b,basis):
            return None
    return tuple(basis.values())


def _restrict(cells,bit):
    result=[]
    for w,rows in cells:
        new=_basis((a>>1,b^((a&1)*bit)) for a,b in rows)
        if new is not None:
            result.append((w,new))
    return tuple(result)


def _mean(cells):
    return sum((w/Fraction(1<<len(rows)) for w,rows in cells),Fraction())


def _inner(f,g):
    total=Fraction()
    for w,rows in f:
        for v,other in g:
            both=_basis((*rows,*other))
            if both is not None:
                total+=w*v/Fraction(1<<len(both))
    return total


@dataclass
class Node:
    raw: tuple
    mean: Fraction
    variance: Fraction
    low: tuple = ()
    high: tuple = ()
    edges: tuple = ()


class AffineEdgeCache:
    """Each cell is (weight, [(nonnegative variable mask, rhs), ...]).

    Variables are queried from least to most significant. extrema() returns
    ((minimum, assignment), (maximum, assignment)). Assignments are bit masks.
    """
    def __init__(self,n,cells):
        if not isinstance(n,int) or n<0:
            raise ValueError("invalid dimension")
        self.layers=[[] for _ in range(n+1)]
        terms=[]
        for weight,flat in cells:
            rows=list(flat)
            if any(not isinstance(a,int) or not 0<=a<1<<n or b not in (0,1) for a,b in rows):
                raise ValueError("invalid affine equation")
            rows=_basis(rows)
            if rows is not None and weight:
                terms.append((Fraction(weight),rows))
        self.root=self._intern(0,tuple(terms))

    def _intern(self,depth,raw):
        mean=_mean(raw)
        variance=_inner(raw,raw)-mean**2
        if not variance:
            return (None,Fraction(),mean)
        for previous in self.layers[depth]:
            cov=_inner(raw,previous.raw)-mean*previous.mean
            if cov**2==variance*previous.variance:
                a=cov/previous.variance
                return previous,a,mean-a*previous.mean
        node=Node(raw,mean,variance)
        self.layers[depth].append(node)
        node.edges=tuple(self._intern(depth+1,_restrict(raw,b)) for b in (0,1))
        for maximize in (False,True):
            options=[]
            for bit,edge in enumerate(node.edges):
                value,suffix=self._edge_extreme(edge,maximize)
                options.append((value,(suffix<<1)|bit))
            # On ties retain the numerically smallest witness.
            choice=min(options,key=lambda z: (-z[0] if maximize else z[0],z[1]))
            if maximize:
                node.high=choice
            else:
                node.low=choice
        return node,Fraction(1),Fraction()

    @staticmethod
    def _edge_extreme(edge,maximize):
        child,a,b=edge
        if child is None:
            return b,0
        value,mask=child.high if maximize==(a>0) else child.low
        return a*value+b,mask

    def extrema(self):
        return tuple(self._edge_extreme(self.root,flag) for flag in (False,True))

    def value(self,assignment):
        if not isinstance(assignment,int) or not 0<=assignment<1<<(len(self.layers)-1):
            raise ValueError("assignment outside declared universe")
        node,a,b=self.root
        while node is not None:
            node,k,c=node.edges[assignment&1]
            b+=a*c
            a*=k
            assignment>>=1
        return b

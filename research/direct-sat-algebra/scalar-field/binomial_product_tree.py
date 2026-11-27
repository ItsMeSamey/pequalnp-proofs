"""Bounded-width products of sparse inequations on affine binomial models.

solve(field,n,equations,polynomials,tree=None,max_width=None,max_products=None)
returns Result(status,peak_width,products,reason). Trees nest pairs of nodes,
with zero-based leaf indices used exactly once. None chooses a balanced tree.
max_width bounds surviving classes per node; max_products bounds cumulative
raw pair products at internal nodes. Exhaustion gives UNKNOWN. Leaf input
length is charged separately. No discrete logarithms or assignments are used.
"""
from dataclasses import dataclass
from affine_binomial import least_support_count
from binomial_inequation import ratio


@dataclass(frozen=True)
class Result:
    status: str
    peak_width: int
    products: int
    reason: str = ""


class Reducer:
    def __init__(self,field,n,equations):
        if type(n) is not int or n<0:
            raise ValueError("invalid dimension")
        self.field,self.n=field,n
        self.eq=tuple(tuple(self.term(t) for t in pair) for pair in equations)
        if any(len(pair)!=2 for pair in self.eq):
            raise ValueError("expected two terms per equation")
        self.closures={}
        self.rows={}

    def term(self,t):
        c,ex=t
        ex=tuple(ex)
        if type(c) is not int or not 0<=c<self.field.size or len(ex)!=self.n or any(
                type(k) is not int or k<0 for k in ex):
            raise ValueError("invalid monomial")
        N=self.field.size-1
        return c,tuple(1+(k-1)%N if k else 0 for k in ex)

    def closure(self,mask):
        if mask not in self.closures:
            one=(1,(0,)*self.n)
            pins=tuple(((1,tuple((self.field.size-1)*int(i==j) for j in range(self.n))),one)
                       for i in mask)
            s,models=least_support_count(self.field,self.n,(*self.eq,*pins))
            self.closures[mask]=s if models else None
        return self.closures[mask]

    def active_rows(self,s):
        if s not in self.rows:
            active=set(s)
            rows=[]
            values=[]
            for (a,p),(b,q) in self.eq:
                if a and b and all(i in active or k==0 for i,k in enumerate(p)):
                    rows.append(tuple(p[i]-q[i] for i in s))
                    values.append(self.field.mul(b,self.field.inverse(a)))
            self.rows[s]=rows,values
        return self.rows[s]

    def reduce(self,terms):
        """One input representative per surviving closure/character class.

        The representative comes from this expression. Width is intrinsic to
        its model function; the particular representative can vary by input.
        """
        raw={}
        for t in terms:
            c,ex=self.term(t)
            raw[ex]=raw.get(ex,0)^c
        groups={}
        for ex,c in sorted(raw.items()):
            if not c:
                continue
            s=self.closure(tuple(i for i,k in enumerate(ex) if k))
            if s is None:
                continue
            classes=groups.setdefault(s,[])
            rows,constants=self.active_rows(s)
            for j,(old,weight) in enumerate(classes):
                scale=ratio(self.field,rows,constants,tuple(ex[i]-old[i] for i in s))
                if scale is not None:
                    classes[j]=(old,weight^self.field.mul(c,scale))
                    break
            else:
                classes.append((ex,c))
        return tuple((c,ex) for s in sorted(groups) for ex,c in groups[s] if c)


def solve(field,n,equations,polynomials,tree=None,*,max_width=None,max_products=None):
    for cap in (max_width,max_products):
        if cap is not None and (type(cap) is not int or cap<0):
            raise ValueError("invalid budget")
    reducer=Reducer(field,n,equations)
    polys=list(polynomials)
    if not polys:
        if tree is not None:
            raise ValueError("empty list has no tree")
        polys=[[(1,(0,)*n)]]
    if tree is None:
        nodes=list(range(len(polys)))
        while len(nodes)>1:
            nodes=[(nodes[j],nodes[j+1]) if j+1<len(nodes) else nodes[j]
                   for j in range(0,len(nodes),2)]
        tree=nodes[0]
    # Validate the supplied schedule before any budgeted evaluation.
    stack=[(tree,False)]
    leaves=set()
    post=[]
    while stack:
        node,done=stack.pop()
        if done:
            post.append(None)
        elif type(node) is int:
            if node in leaves or not 0<=node<len(polys):
                raise ValueError("repeated or out-of-range leaf")
            leaves.add(node)
            post.append(node)
        elif isinstance(node,tuple) and len(node)==2:
            stack.extend(((node,True),(node[1],False),(node[0],False)))
        else:
            raise ValueError("invalid tree")
    if len(leaves)!=len(polys):
        raise ValueError("missing leaf")
    values=[]
    peak=products=0
    for leaf in post:
        if leaf is None:
            right,left=values.pop(),values.pop()
            required=len(left)*len(right)
            if max_products is not None and products+required>max_products:
                return Result("UNKNOWN",peak,products,"product budget")
            products+=required
            raw=((field.mul(a,b),tuple(i+j for i,j in zip(p,q)))
                 for a,p in left for b,q in right)
        else:
            raw=polys[leaf]
        reduced=reducer.reduce(raw)
        peak=max(peak,len(reduced))
        if max_width is not None and peak>max_width:
            return Result("UNKNOWN",peak,products,"width budget")
        if not reduced:
            return Result("UNSAT",peak,products)
        values.append(reduced)
    return Result("SAT",peak,products)


def self_test():
    from punctured_witness import BinaryField
    from itertools import combinations,product
    from affine_binomial import power
    from random import Random
    class Binary:
        size=2
        mul=staticmethod(lambda a,b:a&b)
        inverse=staticmethod(lambda a:1 if a else 1//0)
    f=Binary()
    for n in range(1,8):
        polys=[[(1,(0,)*(n+1)),(1,tuple(int(j==0 or j==i+1) for j in range(n+1)))]
               for i in range(n)]
        ans=solve(f,n+1,[],polys)
        assert ans.status=="SAT" and ans.peak_width==1<<n
        assert solve(f,n+1,[],polys,max_width=(1<<n)-1).status=="UNKNOWN"
    f=BinaryField(7)
    n=4
    ex=lambda i,k:tuple(k*int(i==j) for j in range(n))
    eq=[((1,ex(i,3)),(1,(0,)*n)) for i in range(n)]
    polys=[[(1,ex(i,1)),(1,ex(j,1))] for i,j in combinations(range(n),2)]
    a=solve(f,n,eq,polys)
    b=solve(f,n,eq,polys[:-1])
    assert a.status=="UNSAT" and b.status=="SAT"
    assert solve(f,n,eq,polys,max_products=0).status=="UNKNOWN"
    assert solve(f,0,[],[])==Result("SAT",1,0)
    rng=Random(282)
    def value(poly,x):
        acc=0
        for a,p in poly:
            for v,k in zip(x,p):
                a=f.mul(a,power(f,v,k))
            acc^=a
        return acc
    for _ in range(40):
        n=2
        def term():
            return rng.randrange(4),(rng.randrange(5),rng.randrange(5))
        eq=[(term(),term()) for _ in range(rng.randrange(4))]
        pp=[[term() for _ in range(rng.randrange(1,5))] for _ in range(3)]
        reducer=Reducer(f,n,eq)
        models=[x for x in product(range(4),repeat=n) if all(
                        value([p],x)==value([q],x) for p,q in eq)]
        for p in pp:
            result=reducer.reduce(p)
            assert all(value(p,x)==value(result,x) for x in models)
        assert (solve(f,n,eq,pp,(0,(1,2))).status=="SAT")==any(
                    all(value(p,x) for p in pp) for x in models)
    print(f"star widths 2..128; one-closure K4 {a.status}, K4−e {b.status}; 40 exact-model controls")


if __name__=='__main__':
    self_test()

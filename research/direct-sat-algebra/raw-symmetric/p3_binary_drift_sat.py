"""CNF reduction to product equations on disjoint P3s with binary-affine drift.

Row i has the GateSystem format plus sum(a*x_k^2 for k,a in squares[i]).
Missing square lists are empty. A zero-target witness projects to a CNF model.
"""
from dataclasses import dataclass
from star_drift_sat import GateSystem


@dataclass
class System(GateSystem):
    squares: dict
    clauses: tuple

    def check(self,field,values):
        if len(values)!=self.vertices or any(not 0<=x<field.size for x in values):
            return False
        for r,(i,j,c,terms) in enumerate(self.rows):
            z=c^field.mul(values[i],values[j])
            for k,a in terms:
                z^=field.mul(a,values[k])
            for k,a in self.squares.get(r,()):
                z^=field.mul(a,field.mul(values[k],values[k]))
            if z:
                return False
        return True

    def recover(self,field,values):
        if not self.check(field,values):
            return None
        x=tuple(values[:self.master_count])
        if any(v not in (0,1) for v in x) or not all(
                any(x[abs(l)-1]==int(l>0) for l in clause) for clause in self.clauses):
            raise ArithmeticError("invalid projected model")
        return x


def compile_cnf(field,n,clauses):
    if type(n) is not int or n<0:
        raise ValueError("invalid variable count")
    clauses=tuple(tuple(clause) for clause in clauses)
    a=next(1<<i for i in range(field.m) if field.trace(1<<i))
    rows,recipes,squares=[],[],{}
    def fresh(rule,*args):
        v=n+len(recipes)
        recipes.append((rule,args))
        return v
    def affine(c,terms):
        b,y,z=(fresh("zero") for _ in range(3))
        squares[len(rows)]=((y,1),(b,a))
        rows.extend(((b,y,0,()),(b,z,c,tuple(terms))))
    def edge(i,j,c,terms):
        rows.extend(((i,j,c,terms),(i,fresh("zero"),0,())))
    def attach(v):
        edge(v,fresh("zero"),0,())

    def negate(x):
        z=fresh("not",x)
        affine(1,((x,1),(z,1)))
        attach(z)
        return z

    def both(x,y):
        z=fresh("and",x,y)
        left=fresh("copy",x)
        right=fresh("copy",y)
        affine(0,((left,1),(x,1)))
        affine(0,((right,1),(y,1)))
        edge(left,right,0,((z,1),))
        attach(z)
        return z

    for x in range(n):
        y=fresh("copy",x)
        affine(0,((x,1),(y,1)))
        edge(x,y,0,((x,1),))  # x(x+1)=0 after y=x

    for clause in clauses:
        bad=None
        for literal in clause:
            if type(literal) is not int or not 1<=abs(literal)<=n:
                raise ValueError("invalid signed literal")
            x=abs(literal)-1
            fails=negate(x) if literal>0 else x
            bad=fails if bad is None else both(bad,fails)
        if bad is None:
            affine(1,())
        else:
            affine(0,((bad,1),))
    return System(n+len(recipes),rows,recipes,n,squares,clauses)


def check():
    from itertools import product
    from random import Random
    from punctured_witness import BinaryField
    rng=Random(1281)
    cases=[(0,()),(0,[()]),(2,[(1,),(-1,)]),(2,[(1,-1),(2,2)])]
    for _ in range(20):
        n=rng.randrange(1,5)
        cases.append((n,[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(5)))
                         for _ in range(rng.randrange(6))]))
    checks=0
    for modulus in (7,11,19):
        f=BinaryField(modulus)
        a=next(1<<j for j in range(f.m) if f.trace(1<<j))
        for b,y in product(range(f.size),repeat=2):
            assert (f.mul(y,y)^f.mul(y,b)^f.mul(a,f.mul(b,b))==0)==(b==y==0)
        for n,cnf in cases:
            sys=compile_cnf(f,n,cnf)
            adj=[set() for _ in range(sys.vertices)]
            for i,j,_,_ in sys.rows:
                assert i!=j and j not in adj[i]
                adj[i].add(j)
                adj[j].add(i)
            assert all(len(edges) in (1,2) for edges in adj)
            assert all(len(adj[w])+len(edges)==3 for edges in adj for w in edges)
            for x in product((0,1),repeat=n):
                sat=all(any(x[abs(l)-1]==int(l>0) for l in clause) for clause in cnf)
                w=sys.extend(f,x)
                assert (w is not None)==sat
                if sat:
                    assert sys.recover(f,w)==x
                checks+=1
    f=BinaryField(7)
    sys=compile_cnf(f,1,[])
    counts=[0]*4
    for v in product(range(4),repeat=sys.vertices):
        x=sys.recover(f,v)
        if x is not None:
            counts[x[0]]+=1
    assert counts==[16,4,0,0]
    print(f'{checks} CNF assignments; P3 shapes, GF4 master fibers and GF4/GF8/GF16 norm controls passed')


if __name__=='__main__':
    check()

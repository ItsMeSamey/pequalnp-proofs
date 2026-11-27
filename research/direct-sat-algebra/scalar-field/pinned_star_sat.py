"""One raw trace-bit pin makes K-affine drift on GF(4) P3/K2 targets NP-complete.

compile_cnf(field,n,clauses) produces one zero-target row x_i*x_j + c +
sum(a*x_k) per distinct polar edge, another single Boolean condition
Tr(t)=0, and O(CNF length + n) vertices/rows. Every unpinned target is
feasible because each star degree is strictly less than 4. Pinned solutions
project to the original Boolean assignments. Free leaves can give multiple
extensions of one assignment, so the reduction is for decision.
"""
from dataclasses import dataclass
from star_drift_sat import GateSystem


@dataclass
class PinnedSystem(GateSystem):
    pin_vertex: int
    pin_mask: int
    zero_centers: tuple

    def check(self,field,values,*,pinned=True):
        return (super().check(field,values) and
                (not pinned or field.trace(values[self.pin_vertex])==0))

    def extend(self,field,inputs):
        if len(inputs)!=self.master_count or any(type(x) is not int or not 0<=x<4 for x in inputs):
            raise ValueError("expected one GF4 element per input")
        return super().extend(field,inputs)


def compile_cnf(field,n,clauses):
    if field.size!=4 or type(n) is not int or n<0:
        raise ValueError("requires GF4 and a nonnegative variable count")
    recipes=[]
    rows=[]
    checks=[]
    masters=list(range(n))

    def fresh(rule,*args):
        i=n+len(recipes)
        recipes.append((rule,args))
        return i

    def negate(x):
        y=fresh("not",x)
        masters.append(y)
        checks.append((1,((x,1),(y,1))))
        return y

    def conjunction(x,y):
        w=fresh("and",x,y)
        masters.append(w)
        i,j=fresh("copy",x),fresh("copy",y)
        rows.append((i,j,0,((w,1),)))
        checks.extend(((0,((i,1),(x,1))),(0,((j,1),(y,1)))))
        return w

    for clause in clauses:
        bad=None
        for literal in clause:
            if type(literal) is not int or not 1<=abs(literal)<=n:
                raise ValueError("invalid literal")
            x=abs(literal)-1
            false_bit=negate(x) if literal>0 else x
            bad=false_bit if bad is None else conjunction(bad,false_bit)
        checks.append((1,()) if bad is None else (0,((bad,1),)))

    # A fresh mate supplies a genuine polar K2 and the Boolean field equation
    # x(x+1)=0 via the affine tie mate=x. This also covers unused variables.
    for x in masters:
        y=fresh("copy",x)
        rows.append((x,y,0,((x,1),)))
        checks.append((0,((y,1),(x,1))))
    if not checks:
        checks.append((0,()))

    # The trace kernel of GF4 is {0,1}. (t+1)c=1 eliminates t=1, then
    # t*d+b_0=0 forces the head of the affine-check chain to vanish.
    t=fresh("zero")
    c=fresh("invert_shift",t,1)
    d=fresh("zero")
    centers=tuple(fresh("zero") for _ in checks)
    rows.extend(((t,c,1,((c,1),)),(t,d,0,((centers[0],1),))))
    for k,(b,(constant,terms)) in enumerate(zip(centers,checks)):
        u=fresh("zero")
        v=fresh("zero")
        rows.append((b,u,constant,terms))
        successor=((centers[k+1],1),) if k+1<len(centers) else ()
        rows.append((b,v,0,successor))
    return PinnedSystem(n+len(recipes),rows,recipes,n,t,field.trace_mask<<(2*t),centers)


def self_test():
    from itertools import product
    from random import Random
    from punctured_witness import BinaryField
    from star_drift_witness import solve
    f=BinaryField(7)
    assert [z for z in range(4) if not f.trace(z)]==[0,1]
    # Enumerate every field assignment to one local forcing implication.
    for t,c,d,b in product(range(4),repeat=4):
        if not f.trace(t) and f.mul(t^1,c)==1 and f.mul(t,d)==b:
            assert t==b==0
    for b,u,v,L,next_b in product(range(4),repeat=5):
        if b==0 and f.mul(b,u)==L and f.mul(b,v)==next_b:
            assert L==next_b==0
    fixtures=[(0,[]),(0,[()]),(2,[(1,),(-1,)]),(3,[(1,-2,3),(-1,2)]),
              (3,[(1,1,-1)]),(3,[]),(2,[(-2,-2),(-1,2),(1,)])]
    rng=Random(511)
    for _ in range(10):
        n=3
        fixtures.append((n,[tuple(rng.choice((-1,1))*rng.randint(1,n)
                                  for _ in range(rng.randint(0,3))) for _ in range(rng.randint(1,4))]))
    count=0
    for n,clauses in fixtures:
        instance=compile_cnf(f,n,clauses)
        graph=[set() for _ in range(instance.vertices)]
        for i,j,_,_ in instance.rows:
            assert i!=j and j not in graph[i]
            graph[i].add(j);graph[j].add(i)
        assert all(1<=len(row)<=2 for row in graph)
        assert all(len(graph[i])==1 or len(graph[j])==1 for i,j,_,_ in instance.rows)
        satisfiable=False
        for inputs in product((0,1),repeat=n):
            truth=all(any(inputs[abs(l)-1]==(l>0) for l in clause) for clause in clauses)
            extension=instance.extend(f,inputs)
            assert (extension is not None)==truth
            if extension is not None:
                assert instance.check(f,extension)
                assert all(extension[i]==0 for i in instance.zero_centers)
                packed=sum(v<<(2*j) for j,v in enumerate(extension))
                assert (packed&instance.pin_mask).bit_count()%2==0
            satisfiable |= truth
            count+=1
        if n:
            assert instance.extend(f,(2,)+(0,)*(n-1)) is None
        unconditional=solve(f,instance.vertices,instance.rows)
        assert unconditional.status=="SAT" and instance.check(f,unconditional.values,pinned=False)
        if not satisfiable:
            assert f.trace(unconditional.values[instance.pin_vertex])==1
    print(f"{len(fixtures)} CNFs, {count} Boolean assignments, local GF4 forcing tables and all unpinned witnesses passed")


if __name__=="__main__":
    self_test()

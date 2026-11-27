"""Uniform signed-CNF reduction to one product plus K-affine drift per row.

compile_cnf(field,n,clauses) takes nonzero signed 1-based literals. The result
uses GateSystem's rows (i,j,constant,terms), each meaning x_i*x_j + constant
+ sum(coeff*x_k) = 0. All coefficients are zero or one. Its tagged product
graph is a disjoint union of four-vertex paths and single edges. The number
of rows/vertices is linear in n + #clauses + #literal occurrences, regardless
of field degree. GateSystem.extend yields a field witness from a Boolean model.
"""
from star_drift_sat import GateSystem


def compile_cnf(field, n, clauses):
    if not isinstance(n,int) or n<0 or field.size<2 or field.size&(field.size-1):
        raise ValueError("expected a binary field and nonnegative input count")
    rows=[]
    recipes=[]

    def fresh(rule,*args):
        vertex=n+len(recipes)
        recipes.append((rule,args))
        return vertex

    def affine(c,terms):
        # uw=1 forces u!=0, hence ub=0 forces b=0, so bd+L=0 forces L=0.
        # No field inversion is required to extend a satisfying assignment.
        b=fresh("zero")
        u=fresh("not",b)
        w=fresh("copy",u)
        d=fresh("zero")
        rows.extend(((u,w,1,()),(u,b,0,()),(b,d,c,tuple(terms))))

    def attach(wire):
        # Gate outputs are already Boolean by induction. Cover their vertex
        # with a private zero witness to keep the common polar radical trivial.
        rows.append((wire,fresh("zero"),0,()))

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
        rows.append((left,right,0,((z,1),)))
        attach(z)
        return z

    for x in range(n):
        y=fresh("copy",x)
        affine(0,((x,1),(y,1)))
        rows.append((x,y,0,((x,1),)))  # x(x+1)=0 after y=x

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
    return GateSystem(n+len(recipes),rows,recipes,n)


def check():
    from itertools import product
    from random import Random
    from punctured_witness import BinaryField
    from quadratic_centroid import independent

    def components(system):
        adj=[set() for _ in range(system.vertices)]
        for u,v,_,_ in system.rows:
            assert u!=v and v not in adj[u]
            adj[u].add(v)
            adj[v].add(u)
        seen=set()
        for i in range(system.vertices):
            if i in seen:
                continue
            comp={i}
            stack=[i]
            while stack:
                v=stack.pop()
                for w in adj[v]-comp:
                    comp.add(w)
                    stack.append(w)
            assert sorted(len(adj[j]) for j in comp) in ([1,1],[1,1,2,2])
            seen.update(comp)
        # Every unit edge output occurs as polarization of its endpoint units.
        # Every input unit has an incident edge. Testing all endpoint pairs
        # is sufficient for full polar span and zero joint radical.
        assert len({frozenset((u,v)) for u,v,_,_ in system.rows})==len(system.rows)
        assert all(adj)

    rng=Random(721)
    cases=[(0,[]),(0,[()]),(2,[(1,-1)]),(2,[(1,),(-1,)]),(3,[(1,1,2),(-2,3)])]
    for _ in range(25):
        n=rng.randrange(1,5)
        clauses=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(5)))
                 for _ in range(rng.randrange(6))]
        cases.append((n,clauses))
    checks=0
    fields=[BinaryField(mod) for mod in (7,11,19,283)]
    for n,clauses in cases:
        snapshot=None
        for f in fields:
            sys=compile_cnf(f,n,clauses)
            components(sys)
            if snapshot is None:
                snapshot=sys
            else:
                assert sys==snapshot  # identical output, including all coefficients
            for x in product((0,1),repeat=n):
                sat=all(any(bool(x[abs(l)-1])==(l>0) for l in clause) for clause in clauses)
                witness=sys.extend(f,x)
                assert (witness is not None)==sat
                if witness is not None:
                    assert tuple(witness[:n])==x and sys.check(f,witness)
                checks+=1
    f=fields[0]
    # Enumerate *all* auxiliary assignments for the isolated master gadget;
    # this verifies soundness independently of the canonical extend() recipes.
    sys=compile_cnf(f,1,[])
    assert sys.vertices==6
    preimages={x:0 for x in range(f.size)}
    for v in product(range(f.size),repeat=6):
        if sys.check(f,v):
            preimages[v[0]]+=1
    assert preimages=={0:12,1:12,2:0,3:0}
    # Exhaustive local cover for L values: accepted iff L=0.
    for L in range(f.size):
        matches=0
        for b,u,w,d in product(range(f.size),repeat=4):
            if f.mul(u,w)==1 and f.mul(u,b)==0 and f.mul(b,d)==L:
                matches+=1
        assert matches==(f.size*(f.size-1) if L==0 else 0)
    # Test binary full polar image and joint radical on the six-vertex chart.
    m=f.m; edges=[(a,b) for a,b,_,_ in sys.rows]; n=sys.vertices*m
    def polar(x,y):
        xx=[(x>>(i*m))&(f.size-1) for i in range(sys.vertices)]
        yy=[(y>>(i*m))&(f.size-1) for i in range(sys.vertices)]
        return sum((f.mul(xx[a],yy[b])^f.mul(xx[b],yy[a]))<<(j*m)
                   for j,(a,b) in enumerate(edges))
    image=[polar(1<<i,1<<j) for i in range(n) for j in range(i)]
    assert len(independent(image))==m*len(edges)
    operator=[sum(polar(1<<i,1<<j)<<(j*m*len(edges)) for j in range(n)) for i in range(n)]
    assert len(independent(operator))==n
    print(f"{checks} Boolean lifts, 120 component/field checks, exhaustive gadgets and binary polar ranks passed")


if __name__=="__main__":
    check()

"""Compile signed CNF into polynomials x_i*x_j + affine_K(x) on disjoint stars."""
from dataclasses import dataclass

@dataclass
class GateSystem:
    vertices: int
    rows: list
    recipes: list
    master_count: int

    def extend(self,field,inputs):
        values=list(inputs)
        for rule,args in self.recipes:
            if rule=='invert_shift':
                source,a=args
                if values[source]==a:
                    return None
                y=field.inverse(values[source]^a)
            elif rule=='and':
                i,j=args
                y=field.mul(values[i],values[j])
            elif rule=='not':
                y=1^values[args[0]]
            elif rule=='copy':
                y=values[args[0]]
            else:
                y=0
            values.append(y)
        return values if self.check(field,values) else None

    def check(self,field,values):
        if len(values)!=self.vertices or any(not 0<=x<field.size for x in values):
            return False
        for i,j,const,terms in self.rows:
            total=field.mul(values[i],values[j])^const
            for k,c in terms:
                total^=field.mul(c,values[k])
            if total:
                return False
        return True


def compile_cnf(field,n,clauses):
    if field.size<4 or n<0:
        raise ValueError('expected binary extension of degree at least two')
    rows=[]
    recipes=[]
    def fresh(rule,*args):
        k=n+len(recipes)
        recipes.append((rule,args))
        return k
    def exclude(x,a):
        y=fresh('invert_shift',x,a)
        rows.append((x,y,1,((y,a),)))
    def affine(const,terms):
        b=fresh('zero')
        for a in range(1,field.size):
            exclude(b,a)
        d=fresh('zero')
        rows.append((b,d,const,tuple(terms)))
    def negate(x):
        v=fresh('not',x)
        affine(1,((x,1),(v,1)))
        return v
    def and_gate(x,y):
        z=fresh('and',x,y)
        left=fresh('copy',x)
        right=fresh('copy',y)
        affine(0,((left,1),(x,1)))
        affine(0,((right,1),(y,1)))
        rows.append((left,right,0,((z,1),)))
        return z
    # Intermediate master wires are forced Boolean by induction, but give
    # every one an exclusion leaf below to avoid isolated polar inputs.
    for x in range(n):
        for a in range(2,field.size):
            exclude(x,a)
    masters=[]
    for clause in clauses:
        bad=None
        for v in clause:
            if not 1<=abs(v)<=n:
                raise ValueError('invalid signed literal')
            x=abs(v)-1
            if v>0:
                x=negate(x)
                masters.append(x)
            if bad is None:
                bad=x
            else:
                bad=and_gate(bad,x)
                masters.append(bad)
        if bad is None:
            affine(1,())
        else:
            affine(0,((bad,1),))
    for x in masters:
        exclude(x,2)
    return GateSystem(n+len(recipes),rows,recipes,n)


if __name__=='__main__':
    from itertools import product
    from punctured_witness import BinaryField
    for modulus in (7,11):
        f=BinaryField(modulus)
        for clauses in ([(1,-2,3),(-1,2)],[(1,),(-1,)],[],[()],[(1,1,-1)]):
            system=compile_cnf(f,3,clauses)
            graph=[set() for _ in range(system.vertices)]
            for i,j,_,_ in system.rows:
                assert i!=j and j not in graph[i]
                graph[i].add(j)
                graph[j].add(i)
            assert all(1<=len(ns)<=f.size for ns in graph)
            assert all(not(len(graph[i])>1 and len(graph[j])>1)
                       for i,ns in enumerate(graph) for j in ns)
            for x in product((0,1),repeat=3):
                truth=all(any(x[abs(v)-1]==(v>0) for v in clause) for clause in clauses)
                assert (system.extend(f,x) is not None)==truth
        for b in range(f.size):
            assert all(any(f.mul(b^a,c)==1 for c in range(f.size))
                       for a in range(1,f.size))==(b==0)
    print('80 constructive Boolean lifts, forest-star bounds and all zero-forcing values checked')

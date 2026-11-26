from itertools import combinations,product

def span(E):
    s={0}
    for x in E:s.update(x^y for y in tuple(s))
    return s
W={0,4,8,12}; H={0,1,2,3}; U=set(range(16)); A,B=16,32
E={a^w for a in (A,B) for w in W-{0}}|{A^B^w for w in W}
def tables(E):
    out=set()
    for i,j in combinations(E,2):
        S=span([i,j])
        if len({x>>4 for x in S})<4:continue
        out.add(tuple(next(t&15 for t in S if t>>4==q>>4) for q in (A,B)))
    return out
def feasible(E):
    return any(span((*C,A^1,B^2))&U==H for n in range(len(E)+1) for C in combinations(E,n))
old,new=tables(E),tables(E|{A})
assert old==set(product(W,repeat=2))-{(0,0)} and new-old=={(0,0)}
assert not feasible(E) and feasible(E|{A})
def bit(x):return x.bit_count()&1
for l in U:
    images=lambda T:{(bit(l&a),bit(l&b)) for a,b in T}
    assert images(old)==images(new)
for l,m,k in product(U,U,U):
    def det(a,b):
        return ((bit(l&a)^(k&1))*(bit(m&b)^((k>>3)&1)))^((bit(l&b)^((k>>1)&1))*(bit(m&a)^((k>>2)&1)))
    assert {det(*t) for t in old}=={det(*t) for t in new}
p=A^B^4
project=lambda x:min(x,x^p)
assert {project(x) for x in span([A,4,8]) if x}=={project(x) for x in E if x!=p}
print('15/16 tables, exact H, determinant and scalar masks, Fano minor passed')

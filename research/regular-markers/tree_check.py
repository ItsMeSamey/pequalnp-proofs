"""Binary sum-tree label checker. Run with Python 3."""
from itertools import product
from collections import defaultdict
from random import Random

edges = [(0, 1, 3), (0, 2, 1), (1, 3, 1), (1, 4, 0)]
sizes = [3, 3, 2, 2, 3]
inc = [[(e, w) for e, (u, v, w) in enumerate(edges) if i in (u,v)]
       for i in range(5)]
virtual = [sum(w for _, w in item) for item in inc]
widths = [a+b for a,b in zip(virtual,sizes)]
offsets = [sum(sizes[:i]) for i in range(5)]

def span(rows):
    s = {0}
    for r in rows:
        s |= {x ^ r for x in s}
    return s

def orth(s,w):
    return {x for x in range(1<<w) if all((x&y).bit_count()%2==0 for y in s)}

def ports(i,x):
    out = {}
    for e,w in inc[i]:
        out[e] = x & ((1<<w)-1)
        x >>= w
    return out

def global_space(spaces):
    choices = [[(ports(i,x),(x>>virtual[i])<<offsets[i]) for x in s]
               for i,s in enumerate(spaces)]
    return {sum(z for _,z in rows) for rows in product(*choices)
            if all(rows[u][0][e]==rows[v][0][e] for e,(u,v,_) in enumerate(edges))}

def label(bits,weights):
    out=0
    for j,w in enumerate(weights):
        if bits & (1<<j):
            out ^= w
    return out

def dp(i,parent,spaces,duals,A,B):
    children = [(e,dp(v,e,spaces,duals,A,B)) for e,(u,v,w) in enumerate(edges) if u==i]
    table = defaultdict(set)
    for c,d in product(spaces[i],duals[i]):
        if c & d:
            continue
        p,q = ports(i,c), ports(i,d)
        if any(w==3 and p[e].bit_count()>1 for e,w in inc[i]):
            continue
        val = label((c>>virtual[i])<<offsets[i],A)^label((d>>virtual[i])<<offsets[i],B)
        vals = {val}
        for e,child in children:
            vals = {x^y for x in vals for y in child.get((p[e],q[e]),())}
        table[(p.get(parent,0),q.get(parent,0))].update(vals)
    return table

def run():
    rng=Random(481)
    mismatches=0
    for trial in range(150):
        spaces=[]
        for i,w in enumerate(widths):
            rows=[rng.randrange(1<<w) for _ in range(rng.randrange(1,4))]
            if i in (0,1):
                rows.append(7)
            spaces.append(span(rows))
        duals=[orth(s,w) for s,w in zip(spaces,widths)]
        real=sum(sizes)
        C=global_space(spaces)
        D=orth(C,real)
        assert global_space(duals)==D
        A,B=[[rng.randrange(16) for _ in range(real)] for _ in range(2)]
        want={label(c,A)^label(d,B) for c,d in product(C,D) if not c&d}
        got=dp(0,None,spaces,duals,A,B)[(0,0)]
        assert got<=want
        if got!=want:
            mismatches+=1
            if mismatches==1:
                print("first mismatch",trial,spaces,A,B,sorted(want-got))
    assert mismatches == 0
    print("150 random instances passed")
    triangle = [(0,1),(1,2),(2,0)]
    k4 = triangle + [(0,3),(1,3),(2,3),(1,3)]
    def cycles(edge_list):
        result = set()
        for mask in range(1<<len(edge_list)):
            parity = 0
            for j,(u,v) in enumerate(edge_list):
                if mask & (1<<j):
                    parity ^= (1<<u) ^ (1<<v)
            if parity == 0:
                result.add(mask)
        return result
    spaces = [cycles(es) for es in (k4,k4,triangle,triangle,triangle)]
    duals = [orth(s,w) for s,w in zip(spaces,widths)]
    C = global_space(spaces)
    D = orth(C,sum(sizes))
    assert global_space(duals)==D
    # Independent coordinate bits make the label encode the entire real pair.
    n = sum(sizes)
    A = [1<<j for j in range(n)]
    B = [1<<(n+j) for j in range(n)]
    want = {label(c,A)^label(d,B) for c,d in product(C,D) if not c&d}
    assert dp(0,None,spaces,duals,A,B)[(0,0)] == want
    print("graphic tree: exact recovery of",len(want),"disjoint pairs")

if __name__=="__main__":
    run()

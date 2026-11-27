"""Compile grouped CNF affine equations and residual clauses to one labelled matching.
Literals (variable, negation), variables numbered 0..n-1. Independent DP and backlift.
"""
from collections import defaultdict

def dot(a,b):
    return (a & b).bit_count() & 1

def insert(rows, mask, rhs):
    while mask:
        i=mask.bit_length()-1
        if i not in rows:
            rows[i]=(mask,rhs)
            return True
        m,b=rows[i]; mask ^= m; rhs ^= b
    return not rhs

def solve_rows(rows):
    x=0
    for i,(m,b) in sorted(rows.items()):
        if dot(m,x)!=b: x ^= 1<<i
    return x

def affine_rows(key, accepted):
    base=accepted[0]; basis={}
    for t in accepted:
        insert(basis,t^base,0)
    if len(accepted)!=1<<len(basis): return None
    out=[]
    for mask in range(1,1<<len(key)):
        if all(not dot(mask,t^base) for t in accepted):
            out.append((sum(1<<v for j,v in enumerate(key) if mask>>j & 1),dot(mask,base)))
    return out

def rem(rows,m,b):
    for i in sorted(rows,reverse=True):
        if m>>i & 1:
            a,t=rows[i]; m ^= a; b ^= t
    return m,b

def compile_matching(n,formula):
    blocks=defaultdict(list)
    for c in formula:
        if len(c)>3: raise ValueError("This implementation supports width three.")
        blocks[tuple(sorted({v for v,_ in c}))].append(c)
    linear={}; pending=[]
    for key,cs in blocks.items():
        possible=[p for p in range(1<<len(key)) if all(
            any(((p>>key.index(v))&1)^neg for v,neg in c) for c in cs)]
        if not possible: return None
        rows=affine_rows(key,possible)
        if rows is None: pending.extend(cs)
        elif not all(insert(linear,m,b) for m,b in rows): return None
    # A surviving clause excludes exactly the common zero of its literal forms.
    local=[]; seen=set()
    for c in pending:
        eq={}
        if not all(insert(eq,*rem(linear,1<<v,neg)) for v,neg in c): continue
        if not eq: return None
        normal=tuple(rem({j:val for j,val in eq.items() if j<i},m,b)
                     for i,(m,b) in sorted(eq.items()))
        if normal not in seen:
            local.append(normal); seen.add(normal)
    # Local z=Wx. Clause excludes its indicated RHS h_i. Triangles miss all ones.
    rows=[]; offset=0; edges=[]
    for block in local:
        first=len(rows)
        for m,b in block:
            if not b: offset |= 1<<len(rows)
            rows.append(m)
        for j in range(1,len(block)):
            edges.append((1<<first,1<<(first+j)))
    # N spans the left kernel of W; represent each syndrome as its dot products.
    elim={}; null=[]
    for i,m in enumerate(rows):
        coeff=1<<i
        while m:
            h=m.bit_length()-1
            if h not in elim:
                elim[h]=m,coeff
                break
            q,c=elim[h]; m ^= q; coeff ^= c
        if not m: null.append(coeff)
    def syndrome(v):
        return sum(dot(v,a)<<i for i,a in enumerate(null))
    return linear,rows,offset,edges,[(syndrome(a),syndrome(b)) for a,b in edges],syndrome(offset),len(null)

def decide(n,f):
    instance=compile_matching(n,f)
    if instance is None: return None
    linear,rows,offset,edges,labeled,target,_=instance
    prev=[{0:None}]
    for a,b in labeled:
        nxt={}
        for before in prev[-1]:
            for j,d in enumerate((0,a,b)):
                nxt.setdefault(before^d,(before,j))
        prev.append(nxt)
    if target not in prev[-1]: return None
    z=offset
    for k in reversed(range(len(edges))):
        target,choice=prev[k+1][target]
        if choice: z ^= edges[k][choice-1]
    eq=dict(linear)
    assert all(insert(eq,row,z>>j&1) for j,row in enumerate(rows))
    x=solve_rows(eq)
    assert all(any(((x>>v)&1)^s for v,s in c) for c in f)
    return x

if __name__=='__main__':
    from random import Random
    rng=Random(9582)
    yes=no=0
    for n in range(1,6):
        for i in range(120):
            f=[[(rng.randrange(n),rng.randrange(2)) for _ in range(rng.randrange(1,4))]
               for _ in range(rng.randrange(1,13))]
            expected=any(all(any((x>>v&1)^s for v,s in c) for c in f) for x in range(1<<n))
            assert expected==(decide(n,f) is not None)
            yes+=expected; no+=not expected
    for m in (1,4,12,50):
        f=[[(2*i+j,p>>j&1) for j in range(3)] for i in range(m) for p in range(8) if p.bit_count()%2]
        inst=compile_matching(2*m+1,f)
        assert inst[-1]==len(inst[3])==0 and decide(2*m+1,f) is not None
    disjoint=[[(3*i+j,0) for j in range(3)] for i in range(40)]
    inst=compile_matching(120,disjoint)
    assert inst[-1]==0 and len(inst[3])==80 and decide(120,disjoint) is not None
    print('random YES/NO',yes,no,'four XOR chains rank zero; 40 disjoint positive clauses rank zero')

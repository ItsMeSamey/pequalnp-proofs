"""Prune prefix syndrome states by the affine span of all suffix options."""
from clause_triangles import compile_matching, insert, solve_rows, dot
from random import Random

def cut_decide(n,f):
    inst=compile_matching(n,f)
    if inst is None: return None,0,0
    lin,forms,off,physical,edges,target,r=inst
    entries=len(edges)
    suffix=[{} for _ in range(entries+1)]
    for i in reversed(range(entries)):
        basis=dict(suffix[i+1])
        for col in edges[i]: insert(basis,col,0)
        suffix[i]=basis
    def contains(b,v):
        while v:
            h=v.bit_length()-1
            if h not in b: return False
            v ^= b[h][0]
        return True
    if not contains(suffix[0],target): return None,0,0
    levels=[{0:None}]
    maxwidth=0
    prefix={}
    for i,(a,b) in enumerate(edges):
        for col in (a,b): insert(prefix,col,0)
        width=len(prefix)+len(suffix[i+1])-len(suffix[0])
        maxwidth=max(maxwidth,width)
        table={}
        for old in levels[-1]:
            for choice,label in enumerate((0,a,b)):
                v=old^label
                if v not in table and contains(suffix[i+1],target^v):
                    table[v]=old,choice
        assert len(table)<=1<<width
        levels.append(table)
    largest=max(map(len,levels))
    if target not in levels[-1]: return None,maxwidth,largest
    z=off
    for i in reversed(range(entries)):
        target,choice=levels[i+1][target]
        if choice: z ^= physical[i][choice-1]
    eq=dict(lin)
    assert all(insert(eq,row,z>>i&1) for i,row in enumerate(forms))
    x=solve_rows(eq)
    assert all(any(((x>>v)&1)^s for v,s in c) for c in f)
    return x,maxwidth,largest

if __name__=='__main__':
    rng=Random(663)
    yes=no=0
    for n in range(1,7):
        for i in range(120):
            f=[[(rng.randrange(n),rng.randrange(2)) for _ in range(rng.randrange(1,4))]
               for _ in range(rng.randrange(1,15))]
            truth=any(all(any(((x>>v)&1)^s for v,s in c) for c in f) for x in range(1<<n))
            result,w,states=cut_decide(n,f)
            assert (result is not None)==truth
            yes+=truth; no+=not truth
    for m in (4,12,60):
        f=[[(2*i+j,0) for j in range(3)] for i in range(m)]
        result,w,s=cut_decide(2*m+1,f)
        assert result is not None and w<=3 and compile_matching(2*m+1,f)[-1]==m-1
        print('chain',m,'rank',m-1,'width',w,'states',s)
    print('random YES/NO',yes,no)

"""Small-instance gate compiler; exhaustive linear spans simplify preprocessing."""
import random

def coordinates(vectors):
    result={0:0}
    for i,v in enumerate(vectors):
        result.update({x^v:m^(1<<i) for x,m in list(result.items())})
    return result

def independent(vectors):
    reduced=[]; span={0}
    for v in vectors:
        if v not in span:
            reduced.append(v); span|={x^v for x in span}
    return reduced

def compile_tree(rows,tree):
    n=len(rows); zero=n; gates=[]; ranks=[]
    def gate(op,i,j):
        gates.append((op,i,j))
        return n+len(gates)
    def combine(wires,mask):
        use=[x for i,x in enumerate(wires) if mask>>i&1]
        if not use:
            return zero
        z=use[0]
        for x in use[1:]:
            z=gate('xor',z,x)
        return z
    def desired(S):
        return independent([row&S for j,row in enumerate(rows) if not (S>>j&1)])
    def rec(node):
        if isinstance(node,int):
            S=1<<node; B=desired(S)
            return S,B,[node]*len(B),zero
        A,aa,aw,qa=rec(node[0]); B,bb,bw,qb=rec(node[1])
        if len(aa)<len(bb):
            A,B=B,A; aa,bb=bb,aa; aw,bw=bw,aw; qa,qb=qb,qa
        ra,rb=len(aa),len(bb); ranks.append((ra,rb))
        ca,cb=coordinates(aa),coordinates(bb)
        q=gate('xor',qa,qb)
        # Coefficient on each stored A parity is a linear form in B.
        for i,ai in enumerate(aw):
            coeff=sum(1<<j for j,row in enumerate(rows)
                      if B>>j&1 and ca[row&A]>>i&1)
            if coeff:
                q=gate('xor',q,gate('and',ai,combine(bw,cb[coeff])))
        parent=coordinates(desired(A|B))
        lift={z&A:z for z in parent}
        # Build a small-instance list of independent annihilating functionals.
        proj=[ca[v] for v in lift]
        funcs=independent([t for t in range(1,1<<ra)
                           if all((v&t).bit_count()%2==0 for v in proj)])
        for fun in funcs:
            selector=[(ca[v]&fun).bit_count()%2 for v in aa]
            pivot=next(i for i,k in enumerate(selector) if k)
            for j,bit in enumerate(selector):
                if j!=pivot and bit:
                    aa[j]^=aa[pivot]; aw[j]=gate('xor',aw[j],aw[pivot])
            del aa[pivot],aw[pivot]
        P=[]; pw=[]
        for z,wire in zip(aa,aw):
            elem=lift[z]; p=elem&B
            P.append(elem); pw.append(gate('xor',wire,combine(bw,cb[p])) if p else wire)
        for p in independent([z for z in parent if (z&A)==0]):
            P.append(p); pw.append(combine(bw,cb[p]))
        assert set(coordinates(P))==set(parent)
        return A|B,P,pw,q
    _,_,_,root=rec(tree)
    assert len(gates)<=5*sum((a+1)*(b+1) for a,b in ranks)
    return gates,root

rng=random.Random(190)
cases=0
for n in range(2,10):
    for _ in range(16):
        tree=list(range(n)); rows=[0]*n
        while len(tree)>1:
            a=tree.pop(rng.randrange(len(tree)))
            b=tree.pop(rng.randrange(len(tree)))
            tree.append((a,b))
        for i in range(n):
            for j in range(i):
                if rng.randrange(2):
                    rows[i]|=1<<j; rows[j]|=1<<i
        gates,q=compile_tree(rows,tree[0])
        for x in range(1<<n):
            bits=[x>>i&1 for i in range(n)]+[0]
            for op,i,j in gates:
                bits.append(bits[i]^bits[j] if op=='xor' else bits[i]&bits[j])
            expected=sum((x>>i&1)*(rows[i]&x&((1<<i)-1)).bit_count()
                         for i in range(n))%2
            assert bits[q]==expected
        cases+=1
print("Verified tree phase circuits and merge gate budgets on",cases,"layouts.")

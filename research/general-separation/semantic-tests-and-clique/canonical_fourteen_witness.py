"""Physical two-readout solver for the canonical oriented six-site boxes.

solve(rows,drift,edges,labels,target) returns None or one integer mask. Original
exposed positions come first. Each ordered edge (tail,head) gets four private
bits in input edge order. Each labels[i] is a two-bit readout column; target
includes any affine readout constants. Parallel edges are separate boxes.
"""
from itertools import combinations
from random import Random
from role_bipartite_two_marks import bits, solve as role_solve
from fourteen_port_table_check import physical_table


def check_input(rows,drift,edges,labels,target):
    n = len(rows)
    if len(labels)!=n or any(type(c) is not int or not 0<=c<4 for c in labels):
        raise ValueError("provide one two-bit readout column per exposed site")
    if type(target) is not int or not 0<=target<4 or type(drift) is not int or not 0<=drift<1<<n:
        raise ValueError("invalid affine constant")
    if any(type(r) is not int or not 0<=r<1<<n for r in rows):
        raise ValueError("invalid exposed row mask")
    if any(((rows[i]>>j) ^ (rows[j]>>i))&1 for i,j in combinations(range(n),2)):
        raise ValueError("asymmetric exposed drift")
    touched = set()
    for i,j in edges:
        if i==j or any(type(v) is not int or not 0<=v<n for v in (i,j)):
            raise ValueError("invalid oriented edge")
        touched.update((i,j))
    if len(touched)!=n:
        raise ValueError("every exposed site must have an incident box")


def raw_valid(rows,drift,edges,labels,target,word):
    """Evaluate original affine and six-site guards directly, without lookup."""
    check_input(rows,drift,edges,labels,target)
    n=len(rows)
    if type(word) is not int or not 0<=word<1<<(n+4*len(edges)):
        return False
    exposed = word&((1<<n)-1)
    error = drift ^ sum(((row&exposed).bit_count()%2)<<i for i,row in enumerate(rows))
    read = 0
    for i in bits(exposed):
        read ^= labels[i]
    if read!=target:
        return False
    for k,(i,j) in enumerate(edges):
        full = ((exposed>>i)&1) | (((exposed>>j)&1)<<1) | (((word>>(n+4*k))&15)<<2)
        a,b,c,d,e,f = ((full>>site)&1 for site in range(6))
        if c&(a^b) or d&a or e&b or f&(b^1):
            return False
        error ^= (1^c^d)<<i
        error ^= (c^e^f)<<j
    return not error&exposed


def solve(rows,drift,edges,labels,target):
    check_input(rows,drift,edges,labels,target)
    n=len(rows)
    heads = {j for _,j in edges}
    tails = sorted(set(range(n))-heads)
    order = tails + sorted(heads)
    pos = {v:i for i,v in enumerate(order)}
    adj = [0]*len(tails)
    degree = 0
    for i,j in edges:
        if i not in heads:
            adj[pos[i]] |= 1<<pos[j]
            degree ^= 1<<pos[i]
    simple = [sum(((rows[i]>>j)&1)<<pos[j] for j in order if i!=j) for i in order]
    c = sum((((drift>>i)^(rows[i]>>i))&1)<<pos[i] for i in tails)
    perm = role_solve(adj,degree,simple,c,[labels[i] for i in order],target)
    if perm is None:
        return None
    w = sum(1<<order[i] for i in bits(perm))
    exposed = w
    defects = []
    slack = {}
    error = drift ^ sum(((row&w).bit_count()%2)<<i for i,row in enumerate(rows))
    for k,(i,j) in enumerate(edges):
        s = ((w>>i)&1) | (((w>>j)&1)<<1)
        defects.append(int(s==1))
        if s==1:
            error ^= 1<<i
        else:
            slack[i]=(k,1)
        slack[j]=(k,2)
    for i in bits(error&w):
        k,b=slack[i]
        defects[k] ^= b
    _,_,table = physical_table()
    for k,(i,j) in enumerate(edges):
        s = ((exposed>>i)&1) | (((exposed>>j)&1)<<1)
        w |= (table[s,defects[k]]>>2)<<(n+4*k)
    assert raw_valid(rows,drift,edges,labels,target,w)
    return w


def test():
    rng=Random(73512)
    tiny=large=0
    for edges,n in (([(0,1)],2), ([(0,1),(1,0)],2), ([(0,1),(0,1)],2),
                    ([(1,2),(0,1)],3), ([(1,0),(2,0)],3)):
        for _ in range(4):
            rows=[rng.randrange(2)<<i for i in range(n)]
            for i,j in combinations(range(n),2):
                if rng.randrange(2):
                    rows[i] |= 1<<j
                    rows[j] |= 1<<i
            drift=rng.randrange(1<<n)
            labels=[rng.randrange(4) for _ in rows]
            for target in range(4):
                data=rows,drift,edges,labels,target
                ans=solve(*data)
                exists=any(raw_valid(*data,w) for w in range(1<<(n+4*len(edges))))
                assert exists==(ans is not None)
                tiny+=1
    for rep in range(150):
        n=rng.randrange(2,9)
        edges=[(i,(i+1)%n) if rep%3==0 or rng.randrange(2) else ((i+1)%n,i)
               for i in range(n)]
        edges += [rng.choice(edges) for _ in range(3)]
        rows=[rng.randrange(2)<<i for i in range(n)]
        for i,j in combinations(range(n),2):
            if rng.randrange(2):
                rows[i] |= 1<<j
                rows[j] |= 1<<i
        drift=rng.randrange(1<<n)
        labels=[rng.randrange(4) for _ in rows]
        for target in range(4):
            ans=solve(rows,drift,edges,labels,target)
            def projected(w):
                lab=0
                for i in bits(w):
                    lab ^= labels[i]
                if lab!=target:
                    return False
                for i in bits(w):
                    ends=[j for tail,j in edges if tail==i]
                    if any(head==i for _,head in edges) or any(w>>j&1 for j in ends):
                        continue
                    if ((drift>>i)^(rows[i]&w).bit_count()^len(ends))&1:
                        return False
                return True
            assert (ans is not None)==any(projected(w) for w in range(1<<n))
            large+=1
    print(tiny,"raw exhaustive comparisons;",large,"projected comparisons")


if __name__=="__main__":
    test()

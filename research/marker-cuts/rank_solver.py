"""Exact labeled symmetric guard solver on a supplied binary vertex tree."""


def span(vectors):
    values = {0}
    for v in vectors:
        if v not in values:
            values |= {s^v for s in values}
    return values


def solve(rows, labels, tree):
    full = (1<<len(rows))-1

    def node(tree):
        if isinstance(tree, int):
            i = tree
            mask = 1<<i
            outside = rows[i] & ~mask
            ins = (0,mask) if outside else (0,)
            table = {}
            for alpha in ins:
                table[alpha,0] = {0:0}
                if (rows[i]&mask)==alpha:
                    table.setdefault((alpha,outside),{})[labels[i]] = mask
            return mask, table
        u, left = node(tree[0])
        v, right = node(tree[1])
        X=u|v
        Y=full^X
        ins=span(rows[i]&X for i in range(len(rows)) if Y>>i&1)
        ol={b for a,b in left}
        oright={b for a,b in right}
        table={}
        for a in ins:
            for b in ol:
                for c in oright:
                    l=left.get(((a^c)&u,b))
                    r=right.get(((a^b)&v,c))
                    if not l or not r:continue
                    out=table.setdefault((a,(b^c)&Y),{})
                    for p,w in l.items():
                        for q,z in r.items():
                            out[p^q]=w|z
        return X,table
    return node(tree)[1][0,0]


if __name__ == '__main__':
    from random import Random
    rng=Random(118)
    for case in range(1300):
        n=rng.randrange(1,11)
        A=[0]*n
        for i in range(n):
            for j in range(i+1):
                if rng.randrange(2):
                    A[i]|=1<<j
                    A[j]|=1<<i
        t=rng.randrange(1,5)
        labels=[rng.randrange(1<<t) for i in range(n)]
        trees=list(range(n))
        while len(trees)>1:
            left=trees.pop(rng.randrange(len(trees)))
            right=trees.pop(rng.randrange(len(trees)))
            trees.append((left,right))
        out=solve(A,labels,trees[0])
        actual={}
        for x in range(1<<n):
            if all(not (x>>i&1) or not ((r&x).bit_count()%2) for i,r in enumerate(A)):
                p=0
                for i,c in enumerate(labels):
                    if x>>i&1:p^=c
                actual[x]=p
        assert out.keys()==set(actual.values())
        assert all(actual[w]==p for p,w in out.items())
    print('1,300 random symmetric systems and supplied decompositions passed.')

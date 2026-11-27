"""Capped branch differential and literal rank-four two-tag physical controls."""
from itertools import combinations
from random import Random
from component_nullity import bits, dependencies, trace
from thick_tag_solver import basis, combine, reduce_vector
from check_marked_cut_defect import partitions
from omega_signature_cover import signatures, dot, _linear


def differential(n, rng):
    edges=list(combinations(range(n),2))
    N=len(edges)
    uc=[sum(1<<j for j,e in enumerate(edges) if i in e) for i in range(n)]
    C={combine(uc[1:],w) for w in range(1<<(n-1))}
    z=next(v for v in rng.sample(range(1<<N),1<<N) if v not in C)
    trans={z^c for c in C}
    labels=[rng.randrange(8) for _ in edges]
    truth,pure,translated=set(),set(),set()
    # Truth uses physical support masks, including all nonminimal supports.
    for S in range(1<<N):
        truth.add(frozenset(combine(labels,w) for w in C|trans if not w&~S))
    for part in partitions(n):
        cross=sum(1<<j for j,(a,b) in enumerate(edges) if part[a]!=part[b])
        cut_gains={combine(labels,w) for w in C if not w&~cross}
        # Pure branch needs an internal odd triangle.
        if any(len({part[a] for a in tri})==1 and
               sum((z>>j)&1 for j,e in enumerate(edges) if set(e)<=set(tri))%2
               for tri in combinations(range(n),3)):
            pure.add(frozenset(cut_gains))
        for w in trans:
            S=cross|w
            # Require internal zero edges to span each specified part.
            internal=[e for j,e in enumerate(edges) if not S>>j&1]
            reached=set()
            blocks=0
            for a in range(n):
                if a not in reached:
                    blocks+=1
                    reached.add(a)
                    for _ in range(n):
                        for i,j in internal:
                            if i in reached or j in reached:
                                reached.update((i,j))
            if blocks!=len(set(part)):
                continue
            u=combine(labels,w)
            if u in cut_gains or len(cut_gains)!=1<<(blocks-1):
                continue
            translated.add(frozenset(cut_gains|{u^g for g in cut_gains}))
    assert ({frozenset({0})}|pure|translated)==truth
    return len(pure-translated),len(translated-pure)


def physical(pure):
    n=7
    edges=list(combinations(range(n),2))
    N=len(edges)
    cuts=[sum(1<<i for i,e in enumerate(edges) if j in e) for j in range(n)]
    z=1<<edges.index((2,3))
    base=cuts[:-1]+[z]
    w0=cuts[0]
    w1=cuts[1] if pure else z
    S=w0|w1
    order=[w0,w1]+base
    pivots,idx=basis(order)
    private_words=[order[i] for i in idx]
    # Full six-name map assigns the two b coordinates on these witnesses;
    # four independent additional rows give the symplectic image.
    needed=(2,3,4,5,0,1)
    k=len(private_words)
    cols=signatures(private_words,N)
    rows=[_linear([(word,int(j==a)) for j,word in enumerate(private_words)],N)[0]
          for a in needed]
    qrows=dependencies(cols)
    q=signatures(qrows,N)
    labels=signatures(rows,N)
    assert trace(q,labels,S)=={0,16,32,48}
    physical_rows=qrows+rows
    pivots,chosen=basis(physical_rows)
    assert len(chosen)==len(physical_rows)
    checks=dependencies(signatures(physical_rows,N))
    private=signatures(checks,N)
    tags=[((w0>>i)&1)|(((w1>>i)&1)<<1) for i in range(N)]
    assert [combine(tags,w) for w in physical_rows]==[0]*(len(physical_rows)-2)+[1,2]
    pairs=0
    for a,b in combinations(range(1,16),2):
        if b>(a^b) or not dot(a,((b&5)<<1)|((b&10)>>1)):
            continue
        xy=[]
        for v in (a,b):
            coeff=_linear([(q[i],dot(v,labels[i])) for i in bits(S)],len(qrows))[0]
            xy.append(combine(rows,v)^combine(qrows,coeff))
        x,y=xy
        assert not combine(private,x) and not combine(private,y)
        ax,ay=[(reduce_vector(w,pivots)[1]>>len(qrows)) &15 for w in xy]
        assert dot(ax,((ay&5)<<1)|((ay&10)>>1))
        for j in (0,1):
            sol=_linear([(private[i],(tags[i]>>j)&1) for i in bits(x|y)],len(checks))
            assert sol is not None
        pairs+=1
    assert pairs==20


if __name__=="__main__":
    rng=Random(491)
    counts=[differential(n,rng) for n in (4,5) for _ in range(6)]
    assert all(map(sum,zip(*counts)))
    physical(True)
    physical(False)
    print("12 exhaustive K4/K5 instances, pure-only/translate-only target counts:",
          [sum(v) for v in zip(*counts)], "40 physical two-tag pair replays")

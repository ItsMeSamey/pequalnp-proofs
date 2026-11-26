"""Rank-two boundary policies on a supplied binary host."""
from itertools import combinations, product
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[1]/'aggregate-many-ports'))
from baseline import family, basis_indices, canonical, image, solve

def color_sum(a,b,h):
    return ((a&h).bit_count()%2)+2*((b&h).bit_count()%2)

def triangle(cols,port):
    cols=tuple(cols)
    B=basis_indices(cols)
    J=tuple(e for e in range(len(cols)) if e not in B)
    base=tuple(cols[e] for e in B)
    P=tuple(solve(base,p) for p in port)
    if any(p is None for p in P):
        raise ValueError("rank-two port must be spanned")
    cs=tuple(solve(base,cols[j]) for j in J)
    cov=tuple(sum(((p>>i)&1)<<j for j,p in enumerate(P)) for i in range(len(B)))
    rows=tuple(sum(((c>>i)&1)<<j for j,c in enumerate(cs)) for i in range(len(B)))
    def lift(a,b,chords):
        f,g=image(P,a),image(P,b)
        colors=[0]*len(cols)
        for j,c,v in zip(J,cs,chords):
            colors[j]=v
            if v&1:
                f^=c
            if v&2:
                g^=c
        for i,e in enumerate(B):
            colors[e]=((f>>i)&1)+2*((g>>i)&1)
        return tuple(colors)
    records=[]
    mobile=canonical(h for h,r in zip(cov,rows) if r)
    if len(mobile)<2:
        real=[e for i,e in enumerate(B) if rows[i]]+list(J)
        if mobile:
            h,=mobile
            direction=next(v for v in range(1,4) if (v&h).bit_count()%2)
            idx=sum(1<<i for i,r in enumerate(rows) if r)
            p=image(tuple(cols[e] for e in B),image(P,direction)&idx)
            kind,coord=family(tuple(cols[e] for e in real),((0,0),)*len(real),(p,))
            assert kind=='transparent'
        else:
            _,coord=family(tuple(cols[e] for e in real),((0,0),)*len(real),())
        coltypes={h for h,r in zip(cov,rows) if h and not r}
        for a,b in product(range(4),repeat=2):
            v=color_sum(a,b,mobile[0]) if mobile else 0
            colors=[0]*len(cols)
            colored=coord[v&1,v>>1][0]
            for offset,e in enumerate(real):
                colors[e]=colored[offset]
            for i,e in enumerate(B):
                if not rows[i]:
                    colors[e]=color_sum(a,b,cov[i])
            fixed=set(mobile)|{h for h in coltypes if color_sum(a,b,h)}
            trace=frozenset(u for u in range(4) if all((u&h).bit_count()%2==0 for h in fixed))
            records.append(((a,b),None,tuple(colors),trace))
        return 'Y',records
    i,j=next((i,j) for i,j in combinations(range(len(B)),2)
             if rows[i] and rows[j] and cov[i] and cov[j] and cov[i]!=cov[j])
    hi,hj=cov[i],cov[j]
    if rows[i]!=rows[j]:
        chart=family(cols,((0,0),)*len(cols),port)
        assert chart[0]=='transparent'
        return 'affine',[(ab,None,w,frozenset({0})) for ab,(w,_) in chart[1].items()]
    active=[k for k in range(len(J)) if (rows[i]>>k)&1]
    if len(active)>=2:
        q,r=active[:2]
        for a,b in product(range(4),repeat=2):
            chords=[1]*len(J)
            other=(len(active)-2)%2
            chords[q]=2+((color_sum(a,b,hi)&1)^other)
            chords[r]=1+2*(color_sum(a,b,hj)>>1)
            w=lift(a,b,chords)
            assert w[B[i]]&1 and w[B[j]]&2
            records.append(((a,b),None,w,frozenset({0})))
        return 'affine-two-chords',records
    q,=active
    u1=next(u for u in range(1,4) if (u&hi).bit_count()%2 and not (u&hj).bit_count()%2)
    u2=next(u for u in range(1,4) if (u&hj).bit_count()%2 and not (u&hi).bit_count()%2)
    for a,b,z in product(range(4),repeat=3):
        x,y=color_sum(a,b,hi)^z,color_sum(a,b,hj)^z
        if (x,y,z)==(0,0,0):
            continue
        chords=[1]*len(J)
        chords[q]=z
        verified=lift(a,b,chords)
        frozen=tuple(u for u,c in zip((u1,u2,u1^u2),(x,y,z)) if c==0)
        span=frozenset(image(frozen,m) for m in range(1<<len(frozen)))
        records.append(((a,b),z,verified,span))
    return 'triangle',records

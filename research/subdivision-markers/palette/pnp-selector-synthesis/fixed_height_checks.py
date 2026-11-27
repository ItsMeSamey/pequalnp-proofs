from random import Random
from fixed_height import recognize,solve
from recognizer import tag_at,selected_sites
from witness_tests import span,trace

def image(cols,d,s,j):
    """Solve by independent truth-value equations, then compare full private output."""
    size=1 << (2*d)
    work={}
    for i,(k,b,h) in enumerate(cols):
        for mask in range(size):
            if mask.bit_count()>s: continue
            eq=0
            for g in range(size):
                if g&mask!=mask: continue
                # Private value must be constant; for testing a particular u below
                # put u at every chart on the right hand side.
                eq ^= k << (d*g)
                if tag_at(g,k,d)!=b:
                    eq ^= 1 << (d*size+i*size+g)
            if mask.bit_count()>j:
                eq ^= h << ((d+len(cols))*size+2*mask)
            while eq and eq.bit_length() in work:
                eq ^= work[eq.bit_length()]
            if eq: work[eq.bit_length()]=eq
    out=set()
    for u in range(1<<d):
        rhs=sum(u << (d*g) for g in range(size))
        while rhs and rhs.bit_length() in work:
            rhs ^= work[rhs.bit_length()]
        if rhs==0: out.add(u)
    return out

def main():
    rng=Random(7052)
    cases=0
    for d in (0,1,2,3):
        for t in range(8):
            cols=[(1<<i,rng.randrange(4),rng.randrange(4)) for i in range(d)]
            cols += [(rng.randrange(1<<d),rng.randrange(4),rng.randrange(4)) for i in range(4)]
            cols += [(0,0,1),(cols[-1][0],cols[-1][1],cols[-1][2]^2)]
            actual=any(trace(cols,[i for i in range(len(cols)) if m>>i&1])==set(range(4)) for m in range(1<<len(cols)))
            for s,j in ((1,0),(2,0),(2,1),(3,0),(3,1),(3,3)):
                cert=recognize(cols,d,s,j)
                assert span(u for u,c in cert.anchors)==image(cols,d,s,j)
                for u,c in cert.anchors:
                    heights=[]
                    for g in range(1<<(2*d)):
                        x=h=0
                        for i in selected_sites(cert,cols,c,g):
                            x ^= cols[i][0]
                            h ^= cols[i][2]
                        assert x==u
                        heights.append(h)
                    for bit in range(2*d):
                        for idx in range(len(heights)):
                            if idx>>bit&1: heights[idx]^=heights[idx^(1<<bit)]
                    assert all(idx.bit_count()<=j or not h for idx,h in enumerate(heights))
                witness=solve(cols,d,s,j)
                assert (witness is not None)==actual
                if witness is not None: assert trace(cols,witness)==set(range(4)) and len(witness)<=d+2
                cases+=1
    print(cases,'truth-equation image and literal physical decisions passed')
if __name__=='__main__': main()

"""Compare the computed private image to the full space of site truth tables."""
from random import Random
from recognizer import recognize
from witness_tests import span

def reference(cols,d,s):
    n_charts = 1 << (2*d)
    monomials=[sum(1 << g for g in range(n_charts) if g & m == m)
               for m in range(n_charts) if m.bit_count()<=s]
    # Exhaustively generate the entire Boolean polynomial space, then intersect it
    # with each site's allowed support. Small d is intentional.
    polynomials = span(monomials)
    pivots={}
    for k,b,_ in cols:
        allowed=0
        for g in range(n_charts):
            label=tuple(sum(((g >> (a*d+j)) & (k >> j) & 1) for j in range(d))%2 for a in range(2))
            if label==(b&1,b>>1):
                allowed|=1<<g
        for poly in polynomials:
            if poly & ~allowed: continue
            packed=sum(k << (d*g) for g in range(n_charts) if poly>>g&1)
            while packed:
                top=packed.bit_length()-1
                if top not in pivots:
                    pivots[top]=packed
                    break
                packed ^= pivots[top]
    answer=set()
    for k in range(1<<d):
        packed=sum(k<<(d*g) for g in range(n_charts))
        while packed and (packed.bit_length()-1) in pivots:
            packed ^= pivots[packed.bit_length()-1]
        if not packed: answer.add(k)
    return answer

def main():
    rng=Random(4412)
    total=0
    for d in (1,2):
        for case in range(20):
            cols=[(k,rng.randrange(4),0) for k in range(1<<d)] + [(rng.randrange(1<<d),rng.randrange(4),0) for _ in range(6)]
            for s in range(1,4):
                observed=span(u for u,c in recognize(cols,d,s).anchors)
                assert observed==reference(cols,d,s)
                total+=1
    print(total, "private spaces agree with literal truth-table polynomial enumeration")

if __name__=='__main__': main()

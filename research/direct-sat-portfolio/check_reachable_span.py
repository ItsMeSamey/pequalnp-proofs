from random import Random
from reachable_span import solve


def accepts(n,gates,out,word):
    values = 1 | word<<1
    for j,(a,b) in enumerate(gates):
        z = ((values&a).bit_count()%2) * ((values&b).bit_count()%2)
        values |= z << (n+j+1)
    return (values&out).bit_count()%2


def run():
    # x0*x1, then its XOR with x0 as one affine operand. Reuse is carried.
    gates=((2,4),(8|2,1))
    assert solve(2,gates,16,budget=10000,fresh=[[0,1],[]])["status"]=="sat"
    assert solve(2,gates,16,budget=10000,fresh=[[0,1],[0]])["status"]=="skip"
    # Fresh shared raw x0 is not independent across two products.
    eq=((2,4),(2,4))
    assert solve(2,eq,8|16,budget=10000,banks=[2],fresh=[[0,1]])["status"]=="unsat"
    # A genuinely quadratic function of two previous states is outside the chart.
    both=((2,1),(4,1),(8,16))
    assert solve(2,both,32,budget=10000)["status"]=="skip"
    assert solve(2,both,32,budget=10000,banks=[3])["status"]=="sat"
    assert solve(2,both,32,budget=1)["status"]=="skip"
    rng=Random(4053)
    answered=0
    for _ in range(500):
        n=rng.randrange(0,6)
        m=rng.randrange(0,7)
        gates=[(rng.randrange(1<<(n+i+1)),rng.randrange(1<<(n+i+1))) for i in range(m)]
        out=rng.randrange(1<<(n+m+1))
        expected=any(accepts(n,gates,out,x) for x in range(1<<n))
        for banks in (None, [m] if m else []):
            ans=solve(n,gates,out,budget=100000,banks=banks)
            if ans["status"]=="skip":
                continue
            answered+=1
            assert (ans["status"]=="sat")==expected
            if expected:
                assert accepts(n,gates,out,ans["witness"])
    print(1000, "bounded dispatches,", answered, "complete and verified")


if __name__=="__main__":
    run()

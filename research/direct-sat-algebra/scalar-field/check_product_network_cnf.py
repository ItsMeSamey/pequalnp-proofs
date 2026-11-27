"""Begin with real DIMACS clauses and run the ordinary quadratic lift."""
from cnf_quadratic_interface import lift
from hidden_product_network import recover
from product_network_inequality import decide
from quadratic_image import Quadratic, evaluate
from quadratic_target import apply_basis, interpolate


def check():
    n=5
    clauses=[(-(i+1),-((i+1)%n+1)) for i in range(n)]
    lifted=lift(n,clauses)
    assert lifted.variables==n and not lifted.equations
    def dense(z):
        # Compose invertible binary transvections and a translation.
        for i in range(n):
            z ^= ((z>>i)&1) << ((i+1)%n)
        return z
    target=23
    original=lambda x:evaluate(lifted.forms,dense(x)^11)
    encoded=lambda x:target ^ dense(original(x))
    chart=recover(n,n,*interpolate(encoded,n))
    assert chart and chart.field.m==1
    for j,expected in ((1,False),(2,True)):
        c,l,p=interpolate(lambda x: ((dense(x)^11)&1) & (((dense(x)^11)>>j)&1),n)
        form=Quadratic(c,sum(a<<i for i,a in enumerate(l)),tuple(p))
        answer=decide(chart.field,chart.frames,chart.shift,chart.edges,chart.output_offset,target,form)
        brute=any(all(any(bool(x&(1<<(abs(v)-1)))==(v>0) for v in clause)
                      for clause in clauses) and (x&1) and (x>>j&1) for x in range(1<<n))
        assert answer==brute==expected
    for n,cls in ((3,[(1,-2,3)]),(5,[(-1,2,4),(2,-3,5),(1,-4,-5)])):
        h=lift(n,cls)
        raw=interpolate(lambda x:evaluate(h.forms,x),h.variables)
        assert recover(h.variables,len(h.forms),*raw) is None
    print('dense DIMACS 2-SAT cycle SAT and UNSAT side goals; two ordinary 3-SAT gate lifts rejected')


if __name__=='__main__':
    check()

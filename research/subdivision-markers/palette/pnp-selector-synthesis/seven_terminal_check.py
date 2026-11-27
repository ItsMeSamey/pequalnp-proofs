"""Seven-terminal dual controls; small graphs retain parity obstruction only."""
from wedge_path import solve
from wedge_checks import direct
from frontier import basis
from recognizer import bit_indices

def kernel(cols):
    piv,rel={},[]
    for i,x in enumerate(cols):
        z=1<<i
        while x:
            p=x.bit_length()-1
            if p not in piv:
                piv[p]=(x,z)
                break
            a,b=piv[p]
            x^=a
            z^=b
        if not x: rel.append(z)
    return rel

def prepare(edges):
    physical=[(1<<a)^(1<<b) for a,b in edges]
    original=physical+[3,5,15,1|16|32|64]
    rel=kernel(original)
    dual=[sum(((z>>i)&1)<<j for j,z in enumerate(rel)) for i in range(len(original))]
    piv={}
    def reduce(v):
        b=0
        while v and v.bit_length()-1 in piv:
            x,y=piv[v.bit_length()-1]
            v^=x
            b^=y
        return v,b
    for col in dual[-4:]+dual[:-4]:
        x,b=reduce(col)
        if x: piv[x.bit_length()-1]=(x,b^(1<<len(piv)))
    assert [reduce(x)[1] for x in dual[-4:]]==[1,2,4,8]
    raw=[reduce(v)[1] for v in dual[:-4]]
    return [(v>>4,(v>>2)&3) for v in raw],[v&3 for v in raw]

def main():
    cycle=[(i,(i+1)%7) for i in range(7)]
    for cut in range(4):
        cols,h=prepare(cycle+[(0,2),(1,3),(2,4)][:cut])
        reps,w=solve(cols)
        expected,L=direct(cols)
        assert basis(z for u,v,z in reps)==expected
        def hv(z):
            s=0
            for i in bit_indices(z): s^=h[i]
            return s
        assert all(not(hv(u) and hv(v) and hv(u)!=hv(v)) for u,v,z in reps)
        print('N/r/W/w',len(cols),len(L),len(reps),w)
if __name__=='__main__': main()

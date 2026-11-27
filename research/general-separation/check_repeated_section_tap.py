"""Finite physical checks of two distinct section maps on a guarded AMO suffix."""
from itertools import combinations
from check_binary_fault_solver import Source, raw
from linear_tap_separator import _extract
from section_syndrome_cnf import compile_sections


def source():
    # t,b,x,u0,...,u3. F(x)=NOT x, hence #G=3 and #H=15.
    h = 7
    c = Source(h)
    nx = c.inv(2)
    nt = c.inv(0)
    left = c.both(nt,nx)
    right = c.both(c.both(0,1),nx)
    acc = c.nand(c.inv(left),c.inv(right))
    for i,j in combinations(range(3,7),2):
        edge = c.nand(i,j)
        join = c.nand(acc,edge)
        acc = c.inv(join)
    return c.finish(acc),nx,nt


def raw_suffix(h,F):
    gates,out = F
    start = h+len(gates)-18
    taps = set()
    edges = []
    acc = None
    for edge in range(start,start+18,3):
        a,b = gates[edge-h]
        assert 0 <= a < h and 0 <= b < h and a != b
        prev,input_edge = gates[edge+1-h]
        assert input_edge == edge and prev < edge
        if acc is not None:
            assert prev == acc
        assert gates[edge+2-h] == (edge+1,edge+1)
        acc = edge+2
        taps.update((a,b))
        edges.append(tuple(sorted((a,b))))
    assert out == acc and len(taps) == 4
    assert set(edges) == set(combinations(sorted(taps),2))
    factors,_,_ = _extract(h,gates,out)
    live_pairs = {tuple(sorted(f[:2])) for f in factors if len(f)==3}
    assert all(tuple(sorted((1<<(h-a),1<<(h-b)))) in live_pairs for a,b in edges)
    return start


def reject_first(h,F):
    start = raw_suffix(h,F)
    # All possible first-bank memberships, exposing exactly the tested suffix
    # wire first and then all its bank primaries. Later outputs cannot repair
    # a failure to recognize the first wire.
    rejected = 0
    for mask in range(1<<h):
        bank = tuple(i for i in range(h) if mask >> i & 1)
        public = tuple(i for i in range(h) if i not in bank)
        for w in range(start,start+18):
            assert compile_sections(h,F,public,((bank,(w,*bank)),)) is None
            rejected += 1
    return rejected


def chart(h,F,bank,outputs):
    public = tuple(i for i in reversed(range(h)) if i not in bank)
    obj = compile_sections(h,F,public,((bank,outputs),))
    assert obj is not None and obj.width == h and obj.multiplicity == 1
    images = [obj.lift(y) for y in range(1<<h)]
    assert len(set(images)) == 1<<h
    assert all(raw(h,F,x)==raw(h,obj.circuit,y) for y,x in enumerate(images))
    return obj,public,images


def main():
    h = 7
    F,nx,_ = source()
    true = {x for x in range(1<<h) if raw(h,F,x)}
    assert len(true) == 15
    first,pub,lift1 = chart(h,F,(2,3),(nx,3))
    # In the first quotient choose the original NOT(t), then export raw t
    # dependently from it. This differs from reapplying the first map.
    t,u1 = pub.index(0),pub.index(4)
    nt = h+first.circuit[0].index((t,t))
    second,_,lift2 = chart(h,first.circuit,(t,u1),(nt,t,u1))
    composed = {lift1[lift2[y]] for y in range(1<<h) if raw(h,second.circuit,y)}
    assert composed == true
    print('Two section compositions and all original witnesses passed.',flush=True)
    for graph in (F,first.circuit,second.circuit):
        assert reject_first(h,graph) == 18*(1<<h)
    print('All three suffixes retain six raw pairs and reject first suffix cuts.',flush=True)


if __name__=='__main__':
    main()

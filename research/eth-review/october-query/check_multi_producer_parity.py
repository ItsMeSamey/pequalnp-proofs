"""Bounded original-system controls for verification under the shared scheduler."""
from random import Random
from multi_producer_parity import compile_system,reference_join


def trial(n,rows,rhs,groups,owners):
    net=compile_system(n,rows,rhs,groups,owners)
    cap=(1<<net.wires)*(1+sum(1<<len(p.private) for p in net.producers))
    assert reference_join(net,budget=cap-1) is None
    assert cap<=20000
    count,w=reference_join(net,budget=cap)
    good={x for x in range(1<<n) if all((sum((x&m)==m for m in row)&1)==(rhs>>i&1)
                                        for i,row in enumerate(rows))}
    assert count==len(good) and (w in good if count else w is None)
    return net


if __name__=='__main__':
    a=trial(4,[(3,5),(3,),(5,0)],1,[(0,1),(2,)],[(3,),(5,)])
    assert len(a.copies)==1 and a.unused==(3,) and a.wires==5
    trial(3,[(3,),(3,)],1,[(0,),(1,)],[(3,)])
    trial(3,[(3,),(3,)],3,[(0,),(1,)],[(3,)])
    trial(3,[(0,0,1,1)],0,[(0,)],[])
    trial(0,[(),(0,)],0,[(0,1)],[])
    trial(0,[],0,[],[])
    rng=Random(140)
    for rep in range(80):
        n=3
        rows=[[rng.randrange(1<<n) for _ in range(rng.randrange(4))] for j in range(3)]
        mon=sorted({m for row in rows for m in row if m and row.count(m)%2})
        h=[[],[]]
        for m in mon: h[rng.randrange(2)].append(m)
        trial(n,rows,rng.randrange(8),[(2,0),(1,)],h)
    print('86 original parity systems; exact counts, witnesses, shared COPY, joint fibers and cap checks passed')

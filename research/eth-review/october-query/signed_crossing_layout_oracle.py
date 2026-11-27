"""Direct finite-T physical reference on the stated source-cleaned fixture."""
from fractions import Fraction
from math import prod

PACKETS = ((0,None,9,1),(2,6,4,7),(3,8,5,None),(10,None,14,11),(12,13,None,15))

def clauses(sat):
    return ((1,1,-2),(-1,2),(1,),((1,2) if sat else (-1,-2)),(3,-3))

def reference(sat, point, packets=PACKETS):
    # Manual source wiring: x has 4 cleaned occurrences and a 2-node COPY chain.
    # x's internal COPY-COPY edge is old edge 0, x literals are 1..4; y literals 5..7.
    gates = (("or",(2,10),2), ("or",(4,12),1), ("or",(6,),0),
             ("or",(8,14),0 if sat else 3), ("copy",(0,3,5),None),
             ("copy",(1,7,9),None), ("copy",(11,13,15),None))
    L = len(packets[0])
    assert all(len(p)==L for p in packets)
    assert sorted(i for p in packets for i in p if i is not None)==list(range(16))
    denominator = prod(-q for q in range(-L,L) if q)
    weights = {d: prod(point-q for q in range(-L,L) if q!=d)
               for d in range(1-L,L)}
    total = 0
    for word in range(256):
        row = {}
        for packet in packets:
            for i,p in enumerate(packet):
                if p is not None:
                    row[p] = sum(weights[j-i] for j,c in enumerate(packet)
                                 if c is not None and ((word>>(c//2))&1))
        value = 1
        for kind,ports,forbidden in gates:
            gate_sum = 0
            for local in range(1<<len(ports)):
                if kind=="or" and local==forbidden:
                    continue
                if kind=="copy" and local not in (0,(1<<len(ports))-1):
                    continue
                gate_sum += prod(row[p] if ((local>>i)&1) else denominator-row[p]
                                 for i,p in enumerate(ports))
            value *= gate_sum
        total += value
    return Fraction(total,denominator**16)

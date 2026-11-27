"""One genuine signed OR within an otherwise affine parity/COPY network."""
from packet_entry_tape import Ring
from all_center_packet_jets import evaluate


def evaluate_or(edges, packets, base, zeta, *, center, J, vertex, false_word,
                parity=None, sign=0, term_cap=None):
    """false_word bit j is the falsifying y at jth increasing original port on vertex.
    term_cap bounds the total preflight over all underlying parity contractions.
    Returns (J base-ring coefficients, stats) or None before contractions at cap.
    """
    edges=tuple(map(tuple,edges))
    packets=tuple(map(tuple,packets))
    ports=[2*j+i for j,edge in enumerate(edges) for i,v in enumerate(edge) if v==vertex]
    d=len(ports)
    parity={} if parity is None else parity
    if not d or vertex in parity or not 0<=false_word<1<<d:
        raise ValueError('invalid OR gate or competing parity')
    if len(zeta)!=len(base.f)*base.ell or term_cap is not None and term_cap<0:
        raise ValueError('invalid point or term cap')
    # A parity-conditioned d-bit cube has 2^(d-1) characters using the first
    # d-1 ports, since its last bit is determined.
    extra=d-1
    rr=Ring(base.p+extra,base.f,base.ell)
    scale=1<<extra
    lift=tuple(c%(1<<base.p) for c in zeta)
    e=len(edges); vertices=len({v for edge in edges for v in edge})
    kmax=min(2*e,rr.p-e+vertices-1)
    from math import comb
    bound=(2+scale)*sum(comb(2*e,k)*len(packets[0])**k for k in range(kmax+1))
    if term_cap is not None and bound>term_cap:
        return None
    value=[rr.scalar(0) for _ in range(J)]
    work={'calls':0,'terms':0,'term_bound':bound}
    def add_call(target,chars,mult):
        result,st=evaluate(edges,packets,rr,lift,center=center,J=J,
                           parity={**parity,vertex:target},sign=sign^chars)
        for j,c in enumerate(result):
            value[j]=rr.add(value[j],rr.mul(rr.scalar(mult),c))
        work['calls']+=1
        work['terms']+=st['terms']
    for target in (0,1):
        add_call(target,0,scale)
    for subset in range(scale):
        chars=sum(1<<ports[i] for i in range(extra) if subset>>i&1)
        mult=1 if (subset&false_word).bit_count()%2 else -1
        add_call(false_word.bit_count()%2,chars,mult)
    for row in value:
        if any(c%scale for c in row):
            raise ArithmeticError('nonintegral OR projection')
    return tuple(tuple(c//scale for c in row) for row in value),work

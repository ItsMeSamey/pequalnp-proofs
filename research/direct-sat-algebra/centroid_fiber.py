"""Exact fibers of arbitrary packed squarefree binary quadratic maps.

Center and impose the target modulo the polar span before restricting inputs.
Alternate affine output elimination and common radical reduction until the
centroid hypotheses hold. Factor counts multiply and all witness lifts are
recorded. Time is polynomial times the sum of 2^(block output dimension),
including polynomial work in cases with no remaining block.
"""
from quadratic_target import (affine_domain, apply_basis, evaluate_anf, insert,
                              interpolate, prepare, reduce_vector)
from quadratic_centroid import decompose
from quadratic_image import Quadratic, bits
from isotropic_hybrid import count as block_count


def coordinate_map(basis):
    rows = {}
    for j,v in enumerate(basis):
        insert(v,1<<j,rows)
    def encode(value):
        remainder,coords = reduce_vector(value,rows)
        if remainder:
            raise ArithmeticError("output outside coordinate space")
        return coords
    return encode


def count(n,m,constant,linear,pairs,target):
    """Return (exact count, packed original witness or None, output block sizes)."""
    if (min(n,m,target,constant)<0 or len(linear)!=n
            or any(v<0 or v.bit_length()>m for v in (target,constant,*linear,*pairs.values()))
            or any(not (0<=i<j<n) for i,j in pairs)):
        raise ValueError("invalid packed ANF or target")
    original = (constant,tuple(linear),dict(pairs),target)
    lifts = []
    multiplier = 1
    while True:
        target ^= constant
        constant = 0
        span = {}
        for v in pairs.values():
            insert(v,0,span)
        if len(span)<m:
            cols = [reduce_vector(v,span)[0] for v in linear]
            goal = reduce_vector(target,span)[0]
            equations = [(sum(((v>>j)&1)<<i for i,v in enumerate(cols)),(goal>>j)&1)
                         for j in range(m)]
            chart = affine_domain(n,equations)
            if chart is None:
                return 0,None,()
            offset,domain,_ = chart
            def restore(x,offset=offset,domain=domain):
                return offset ^ apply_basis(domain,x)
            lifts.append(restore)
            encode = coordinate_map([v for v,_ in span.values()])
            constant,linear,pairs = interpolate(
                lambda x: encode(evaluate_anf(0,linear,pairs,restore(x))^target),len(domain))
            n,m,target = len(domain),len(span),0
            continue
        if not m:
            total,w,widths = 1<<n,0,()
            break
        # A common radical is the joint kernel of all partial polar derivatives.
        normals = {}
        for (i,j),v in pairs.items():
            for b in bits(v):
                normals[b,i] = normals.get((b,i),0) ^ (1<<j)
                normals[b,j] = normals.get((b,j),0) ^ (1<<i)
        _,radical,_ = affine_domain(n,((v,0) for v in normals.values()))
        if radical:
            forms = tuple(Quadratic(0,sum(((v>>j)&1)<<i for i,v in enumerate(linear)),
                                    tuple(e for e,v in pairs.items() if (v>>j)&1))
                          for j in range(m))
            reduced = prepare(n,forms,target)
            if reduced is None:
                return 0,None,()
            lifts.append(reduced.lift)
            multiplier *= reduced.multiplicity
            n,m,target = reduced.n,len(reduced.forms),reduced.target
            linear = [sum(((f.linear>>i)&1)<<j for j,f in enumerate(reduced.forms))
                      for i in range(n)]
            pairs = {}
            for j,f in enumerate(reduced.forms):
                for e in f.pairs:
                    pairs[e] = pairs.get(e,0) ^ (1<<j)
            constant = sum(f.constant<<j for j,f in enumerate(reduced.forms))
            continue
        blocks = decompose(n,m,0,linear,pairs).blocks
        widths = tuple(len(out) for _,out in blocks)
        encode = coordinate_map([v for _,out in blocks for v in out])
        goal = encode(target)
        total,w = 1,0
        for domain,out in blocks:
            mask = (1<<len(out))-1
            local = coordinate_map(out)
            c,l,q = interpolate(lambda x: local(evaluate_anf(
                0,linear,pairs,apply_basis(domain,x))),len(domain))
            num,model,_ = block_count(len(domain),c,l,q,goal & mask)
            if not num:
                return 0,None,widths
            total *= num
            w ^= apply_basis(domain,model)
            goal >>= len(out)
        break
    for restore in reversed(lifts):
        w = restore(w)
    c,l,q,t = original
    if evaluate_anf(c,l,q,w)!=t:
        raise ArithmeticError("lifted witness fails original target")
    return total*multiplier,w,widths


def self_test():
    from itertools import product,combinations
    from random import Random
    rng = Random(333)
    checked = 0
    def check(n,m,c,l,q):
        nonlocal checked
        vals = [evaluate_anf(c,l,q,x) for x in range(1<<n)]
        for t in range(1<<m):
            hits,w,_ = count(n,m,c,l,q,t)
            assert hits==vals.count(t) and (vals[w]==t if hits else w is None)
            checked += 1
    for n in range(3):
        edges = tuple(combinations(range(n),2))
        for m in range(3):
            for coeff in product(range(1<<m),repeat=1+n+len(edges)):
                check(n,m,coeff[0],coeff[1:1+n],dict(zip(edges,coeff[1+n:])))
    for _ in range(100):
        n,m = rng.randrange(7),rng.randrange(5)
        r = lambda: rng.randrange(1<<m)
        check(n,m,r(),[r() for _ in range(n)],{e:r() for e in combinations(range(n),2)})
    # Three independent scalar blocks plus a free radical direction.
    q = {(2*i,2*i+1):1<<i for i in range(3)}
    assert count(7,3,0,[0]*7,q,7)==(2,63,(1,1,1))
    print(f"{checked} target counts and witnesses plus radical product fixture passed")


if __name__=="__main__":
    self_test()

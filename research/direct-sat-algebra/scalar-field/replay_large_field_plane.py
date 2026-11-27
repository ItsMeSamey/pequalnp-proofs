"""Reproducible dense GF(128)/GF(256) joint raw-ANF to native plane replay."""
from hashlib import sha256
from json import dumps
from random import Random
from time import monotonic
from unittest.mock import patch

import torus_carry_count
from field_plane_chart import fit
from punctured_witness import BinaryField
from quadratic_centroid import independent
from quadratic_image import parity
from quadratic_target import apply_basis, evaluate_anf, insert, interpolate, reduce_vector


def replay(modulus):
    started = monotonic()
    f = BinaryField(modulus)
    rng = Random(54008+f.m)
    n = 2*f.m
    columns = ()
    while len(columns)<n:
        columns = independent((*columns,rng.randrange(1<<n)))
    rows = {}
    for j,col in enumerate(columns):
        insert(col,1<<j,rows)
    shift = rng.randrange(1,1<<n)
    target = rng.randrange(1,f.size)

    def hidden(x):
        rem,z = reduce_vector(x^shift,rows)
        assert not rem
        return target ^ f.mul(z&(f.size-1),z>>f.m)

    c,l,p = interpolate(hidden,n)
    encoded = dumps([f.m,modulus,c,l,sorted((i,j,a) for (i,j),a in p.items()),columns,shift,target],
                    separators=(',',':')).encode()
    instance_hash = sha256(encoded).hexdigest()
    chart = fit(f,1,c,l,p,columns,shift)
    assert chart is not None and chart.outputs==({(0,0):target,(1,1):1},)
    before_count = monotonic()
    with patch.object(torus_carry_count,'point_count',wraps=torus_carry_count.point_count) as native:
        observed = chart.count(target)
        assert native.call_count==1 and native.call_args.args[1]=={(1,1):1}
    count_seconds=monotonic()-before_count
    assert observed==2*f.size-1
    brute=sum(evaluate_anf(c,l,p,x)==target for x in range(1<<n))
    assert observed==brute

    # Pin a nonzero v bit so the witness differs from the chart origin and
    # the two preimage axes are no longer interchangeable.
    raw_row=sum(((reduce_vector(1<<i,rows)[1]>>f.m)&1)<<i for i in range(n))
    pins=[(raw_row,1^parity(raw_row&shift))]
    witness=chart.witness(target,pins)
    assert witness!=shift and parity(raw_row&witness)==pins[0][1]
    assert evaluate_anf(c,l,p,witness)==hidden(witness)==target
    return dict(field_size=f.size,instance_sha256=instance_hash,raw_pair_terms=len(p),
                possible_pairs=n*(n-1)//2,chart_origin=shift,target=target,
                raw_pin=pins[0],raw_witness=witness,native_calls=native.call_count,
                native_polynomial='u*v',exact_count=observed,brute_force_count=brute,
                native_count_seconds=round(count_seconds,6),total_seconds=round(monotonic()-started,3))


if __name__=='__main__':
    for modulus in (131,283):
        print(dumps(replay(modulus),sort_keys=True))

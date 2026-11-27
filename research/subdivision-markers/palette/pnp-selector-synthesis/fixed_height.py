"""Exact fixed-height private-selector image and physical plane decision."""
from functools import reduce
from itertools import combinations
from operator import xor
from pathlib import Path
from runpy import run_path
from recognizer import Certificate, Generator, activation_terms, subset_masks, tag_at

prior = run_path(str(Path(__file__).resolve().parents[1] / 'pnp-chart-hitting.py'))

def recognize(columns, dimension, degree, height_degree):
    if dimension < 0 or not 0 <= height_degree <= degree or degree < 1:
        raise ValueError("invalid dimensions or degree bounds")
    if any(not (0<=k<1<<dimension and 0<=b<4 and 0<=h<4) for k,b,h in columns):
        raise ValueError("invalid physical coordinates")
    if prior['rank'](k for k,b,h in columns) != dimension:
        raise ValueError("compress unobserved private directions first")
    generators, identifiers, equations, outputs = [], {}, {}, {}
    seen = set()
    for site,(key,tag,height) in enumerate(columns):
        # Distinct heights for the same key and tag can cancel high coefficients.
        if (key,tag,height) in seen or (not key and (tag or not height)):
            continue
        seen.add((key,tag,height))
        free = list(range(2*dimension))
        if key:
            pivot = key.bit_length()-1
            free.remove(pivot)
            free.remove(pivot+dimension)
            literal = activation_terms(key, tag, dimension)
            limit = degree-2
        else:
            literal,limit = [0],degree
        for mask in subset_masks(free,limit):
            terms=set()
            for monomial in literal:
                terms.symmetric_difference_update((monomial | mask,))
            constant = key if 0 in terms else 0
            residual=0
            for monomial in terms:
                if monomial == 0:
                    continue
                coefficient = key << 2
                if monomial.bit_count()>height_degree:
                    coefficient |= height
                if coefficient:
                    block=identifiers.setdefault(monomial,len(identifiers))
                    residual ^= coefficient << ((dimension+2)*block)
            chosen = 1 << len(generators)
            generators.append(Generator(site,mask))
            while residual:
                top=residual.bit_length()-1
                if top not in equations:
                    equations[top]=(residual,constant,chosen)
                    break
                old,offset,history=equations[top]
                residual ^= old
                constant ^= offset
                chosen ^= history
            if residual:
                continue
            while constant:
                top=constant.bit_length()-1
                if top not in outputs:
                    outputs[top]=(constant,chosen)
                    break
                old,history=outputs[top]
                constant ^= old
                chosen ^= history
    return Certificate(dimension,degree,generators,list(outputs.values()))

def solve(columns,dimension,degree,height_degree):
    cert=recognize(columns,dimension,degree,height_degree)
    bits=2*dimension
    cap=2*(dimension-len(cert.anchors)+2)
    length_limit=2*height_degree+1
    def candidates():
        if bits <= 2*length_limit*(bits << (cap+1)).bit_length():
            yield from range(1<<bits)
            return
        seeds=prior['seeds'](bits,cap)
        for length in range(1,length_limit+1,2):
            for subset in combinations(seeds,length):
                yield reduce(xor,subset)
    for chart in candidates():
        private,physical,chosen={},{},[]
        for site,(key,tag,height) in enumerate(columns):
            if tag_at(chart,key,dimension)==tag:
                prior['add'](private,key)
                if prior['add'](physical,(key<<2)|height):
                    chosen.append(site)
        if len(physical)-len(private)==2:
            return chosen
    return None

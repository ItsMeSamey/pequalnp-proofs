"""Bound physical search degree from the actual selected section heights."""
from recognizer import activation_terms, bit_indices

def parity_toggle(terms, value):
    if value in terms:
        terms.remove(value)
    else:
        terms.add(value)

def height_anf(columns, certificate, selected):
    coordinates = [set(), set()]
    for index in bit_indices(selected):
        gen = certificate.generators[index]
        k,b,h = columns[gen.site]
        if not h:
            continue
        literal = activation_terms(k,b,certificate.dimension) if k else ([0] if b==0 else [])
        for term in literal:
            monomial = term | gen.free_monomial
            for coord in bit_indices(h):
                parity_toggle(coordinates[coord], monomial)
    return coordinates

def determinant_degree(columns, certificate):
    generators = [[{0},set()],[set(),{0}]]
    generators += [height_anf(columns, certificate, selected) for _,selected in certificate.anchors]
    maximum = 0
    for pos, left in enumerate(generators):
        for right in generators[:pos]:
            terms=set()
            for x,y in ((left[0],right[1]), (left[1],right[0])):
                for a in x:
                    for b in y:
                        parity_toggle(terms,a|b)
            if terms:
                maximum=max(maximum,max(m.bit_count() for m in terms))
    return maximum

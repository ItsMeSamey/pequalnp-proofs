"""Scaled stochastic scalar at h=2^j, reduced modulo 2^precision."""
from collections import Counter, defaultdict
from itertools import combinations


def probe(ports, kinds, length, j, precision):
    if length <= 0 or length & (length-1) or j < 1 or precision < 1:
        raise ValueError("require power-of-two length and positive exponent and precision")
    ell = length.bit_length()-1
    packet = {p:i for i,p in enumerate(dict.fromkeys(p for p,_,_,_ in ports))}
    bits = defaultdict(Counter)
    for p,e,_,_ in ports:
        bits[e][packet[p]] += 1
    result = 0
    for k in range(min(len(ports), (precision-1)//(j+ell))+1):
        shift = k*(j+ell)
        modulus = 1 << (precision-shift)
        h = pow(2, j, modulus)
        for selected in combinations(range(len(ports)), k):
            marked = set(selected)
            pinned = {ports[i][1] for i in selected}
            start = [0]*len(packet)
            for e in pinned:
                for p, multiplicity in bits[e].items():
                    start[p] += multiplicity
            table = {tuple(start):1}
            for e, increments in bits.items():
                if e in pinned:
                    continue
                updated = table.copy()
                for state, weight in table.items():
                    next_state = list(state)
                    for p, value in increments.items():
                        next_state[p] += value
                    key = tuple(next_state)
                    updated[key] = (updated.get(key,0)+weight) % modulus
                table = updated
            subtotal = 0
            for state, weight in table.items():
                terms = {g:[1,1,1] for g in kinds}
                for i,(p,_,g,positive) in enumerate(ports):
                    one = (1-h)*state[packet[p]]
                    a,b = (1,-1) if i in marked else (one,length-one)
                    term = terms[g]
                    if kinds[g] == "copy":
                        term[0] = term[0]*a % modulus
                        term[1] = term[1]*b % modulus
                    else:
                        term[1] = term[1]*(b if positive else a) % modulus
                        term[2] = (0 if i in marked else term[2]*length) % modulus
                for g,(a,b,c) in terms.items():
                    weight = weight*(a+b if kinds[g]=="copy" else c-b) % modulus
                subtotal = (subtotal+weight) % modulus
            result += subtotal << shift
    return result % (1 << precision)

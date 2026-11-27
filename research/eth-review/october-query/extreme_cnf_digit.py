"""A normalized digit of the actual coefficient at t=±(L−1), at zeta=0."""
from partial_shift_affine import character_sum


def _projection(mask, positions):
    return sum(((mask >> index) & 1) << i for i, index in enumerate(positions))


def evaluate(gates, packets, *, center, word_cap=None):
    """Gate triples (kind, ordered_ports, false_word), with None for COPY.

    Ports 2*j and 2*j+1 have the same original column COPY2 bit j.
    For OR, false_word bits are the local falsifying word in port order.
    No unused-variable factor or external sign is included in the physical scalar.
    """
    gates = tuple((kind,tuple(ports),word) for kind,ports,word in gates)
    packets = tuple(tuple(pk) for pk in packets)
    if not packets:
        raise ValueError("supply a packet of the actual width")
    length = len(packets[0])
    if length < 2 or length & (length-1) or any(len(pk) != length for pk in packets):
        raise ValueError("expected uniform power-of-two packet widths")
    if center not in {1-length,length-1}:
        raise ValueError("expected a real extreme center")
    if word_cap is not None and (type(word_cap) is not int or word_cap < 0):
        raise ValueError("expected a nonnegative integer word cap")
    gate_ports = [p for _,ps,_ in gates for p in ps]
    packet_ports = [p for pk in packets for p in pk if p is not None]
    m = len(gate_ports)
    if m % 2 or any(type(p) is not int for p in gate_ports+packet_ports):
        raise ValueError("physical rows must be paired integer ports")
    if sorted(gate_ports) != list(range(m)) or sorted(packet_ports) != list(range(m)):
        raise ValueError("each original port must occur once on each side")
    for kind,ps,word in gates:
        if not ps or kind not in ("or","copy"):
            raise ValueError("expected a nonempty signed OR or COPY")
        if kind == "copy" and word is not None:
            raise ValueError("COPY takes no false word")
        if kind == "or" and (type(word) is not int or not 0 <= word < 1 << len(ps)):
            raise ValueError("invalid OR falsifying word")
    successor = [None]*m
    wrap_read = [None]*m
    wrap = -1 if center > 0 else 1
    for pk in packets:
        for i,row in enumerate(pk):
            if row is None:
                continue
            for d, target in ((center,successor),(wrap,wrap_read)):
                if 0 <= i+d < length and pk[i+d] is not None:
                    target[row] = pk[i+d]//2
    live = sorted({x for x in successor if x is not None})
    live_index = {x:i for i,x in enumerate(live)}
    outside = [x for x in range(m//2) if x not in live_index]
    f = len(outside)
    forms = []
    remaining = []
    for kind,ps,word in gates:
        if kind == "or" and word == 0 and all(successor[p] is None for p in ps):
            mask = 0
            for p in ps:
                if wrap_read[p] is not None:
                    mask ^= 1 << wrap_read[p]
            forms.append((_projection(mask,live),_projection(mask,outside)))
        else:
            positions = tuple(live_index.get(successor[p]) for p in ps)
            remaining.append((kind,positions,word))
    r = len(forms)
    result = {"order":r, "first_bit_position":max(r,f), "live_bits":len(live),
              "outside_bits":f, "word_bound":1 << len(live)}
    if f >= r:
        gram = []
        for _,row in forms:
            gram.append(sum(((row & other).bit_count() & 1) << j
                            for j,(_,other) in enumerate(forms)))
        if character_sum(r,((row,0) for row in gram),0) != 1:
            return dict(result,status="exact",bit=0,visited=0)
    if word_cap is not None and word_cap < result["word_bound"]:
        return dict(result,status="unknown",reason="word_budget",visited=0)
    answer = 0
    for baseline in range(result["word_bound"]):
        for kind,positions,false_word in remaining:
            local = sum(((baseline >> j)&1) << i for i,j in enumerate(positions) if j is not None)
            if kind == "or" and local == false_word:
                break
            if kind == "copy" and local not in (0,(1 << len(positions))-1):
                break
        else:
            if f >= r:
                answer ^= 1
            else:
                eq = [(row,1 ^ ((baseline & offset).bit_count() & 1)) for offset,row in forms]
                answer ^= character_sum(f,eq,0) & 1
    return dict(result,status="exact",bit=answer,visited=result["word_bound"])


def from_clauses(n, clauses, packets, *, center, word_cap=None):
    """Unsplit incidence root; clause port 2*j and variable port 2*j+1 per occurrence j.

    This preserves supplied clauses and literal order. A factor for unused declared
    variables is included in the reported bit position.
    """
    if type(n) is not int or n < 0:
        raise ValueError("expected a nonnegative declared variable count")
    gates = []
    variables = {}
    occurrences = 0
    for clause in clauses:
        ports = []
        false_word = 0
        for i,lit in enumerate(clause):
            if type(lit) is not int or not 1 <= abs(lit) <= n:
                raise ValueError("invalid signed literal")
            ports.append(2*occurrences)
            variables.setdefault(abs(lit),[]).append(2*occurrences+1)
            false_word |= int(lit < 0) << i
            occurrences += 1
        if not ports:
            raise ValueError("empty clause gives the identically zero root")
        gates.append(("or",ports,false_word))
    gates.extend(("copy",ps,None) for ps in variables.values())
    result = evaluate(gates,packets,center=center,word_cap=word_cap)
    result["unused_bits"] = n-len(variables)
    result["first_bit_position"] += result["unused_bits"]
    return result

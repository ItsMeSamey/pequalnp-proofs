"""Deterministic covering-code search for CNFs of normalized width at most three."""
from itertools import product
from math import prod


def _block(length):
    radius = length//4
    size = 1<<length
    offsets = [x for x in range(size) if x.bit_count()<=radius]
    balls = [sum(1<<(c^d) for d in offsets) for c in range(size)]
    uncovered = (1<<size)-1
    centers = []
    while uncovered:
        c = max(range(size),key=lambda i:(balls[i]&uncovered).bit_count())
        centers.append(c)
        uncovered &= ~balls[c]
    return centers


def solve_dense(n,clauses,*,pins=(),node_cap=None):
    """Variables are numbered 1..n. Pins are (variable,bit) pairs or a mapping.
    node_cap covers visited ball-search nodes; cover construction is additional.
    """
    if type(n) is not int or n<0 or (node_cap is not None and
            (type(node_cap) is not int or node_cap<0)):
        raise ValueError("invalid dimension or node cap")
    original = [tuple(row) for row in clauses]
    normalized = []
    for row in original:
        if any(type(x) is not int or not 1<=abs(x)<=n for x in row):
            raise ValueError("literal outside dense variable range")
        unique = tuple(dict.fromkeys(row))
        if not any(-x in unique for x in unique):
            normalized.append(unique)
    fixed = {}
    conflict = False
    for j,bit in pins.items() if hasattr(pins,"items") else pins:
        if type(j) is not int or not 1<=j<=n or type(bit) not in (int,bool) or bit not in (0,1):
            raise ValueError("invalid pin")
        conflict |= j in fixed and fixed[j]!=bit
        fixed[j] = int(bit)
    metrics = dict(active_variables=0,block_lengths=(),center_counts=(),centers=0,
                   radius=0,nodes=0,node_bound=0,centers_visited=0)
    def result(status,word=None):
        return dict(status=status,witness=word,metrics=metrics)
    if conflict:
        return result("UNSAT")
    rows = []
    for row in normalized:
        if any(abs(x) in fixed and fixed[abs(x)]==(x>0) for x in row):
            continue
        row = tuple(x for x in row if abs(x) not in fixed)
        if len(row)>3:
            raise ValueError("residual clause width exceeds three")
        if not row:
            return result("UNSAT")
        rows.append(row)
    active = sorted({abs(x) for row in rows for x in row})
    v = len(active)
    indices = {j:i for i,j in enumerate(active)}
    checks = []
    for row in rows:
        bits = tuple(1<<indices[abs(x)] for x in row)
        checks.append((sum(bits),sum(b for x,b in zip(row,bits) if x<0),bits))
    block = (v+1).bit_length()-1
    lengths = tuple(min(block,v-start) for start in range(0,v,max(1,block)))
    cache = {length:_block(length) for length in sorted(set(lengths))}
    counts = tuple(len(cache[length]) for length in lengths)
    radius = sum(length//4 for length in lengths)
    centers = prod(counts)
    metrics.update(active_variables=v,block_lengths=lengths,center_counts=counts,
                   centers=centers,radius=radius,node_bound=centers*((3**(radius+1)-1)//2))
    pinned = sum(bit<<(j-1) for j,bit in fixed.items())
    for parts in product(*(cache[length] for length in lengths)):
        metrics["centers_visited"] += 1
        center = sum(value<<(i*block) for i,value in enumerate(parts))
        stack = [(center,radius)]
        while stack:
            if node_cap is not None and metrics["nodes"]>=node_cap:
                return result("UNKNOWN")
            word,left = stack.pop()
            metrics["nodes"] += 1
            violated = next((bits for mask,target,bits in checks if word&mask==target),None)
            if violated is None:
                witness = pinned | sum(((word>>i)&1)<<(j-1) for i,j in enumerate(active))
                if (any(all(((witness>>(abs(x)-1))&1)!=(x>0) for x in row) for row in original)
                        or any((witness>>(j-1))&1 != bit for j,bit in fixed.items())):
                    raise ArithmeticError("witness failed original clauses or pins")
                return result("SAT",witness)
            if left:
                stack.extend((word^bit,left-1) for bit in reversed(violated))
    return result("UNSAT")

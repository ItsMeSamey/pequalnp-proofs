"""Compile original CNF to hidden linear selector blocks; literals are one-based."""
from itertools import product


def xor_equivalence(x, y, z):
    return [tuple(-site if bit else site for site, bit in zip((x,y,z), bits))
            for bits in product((0,1), repeat=3) if sum(bits) % 2]


def compile_cnf(n, clauses, *, pin_selectors=False):
    clauses = tuple(tuple(row) for row in clauses)
    if type(n) is not int or n < 0 or any(type(x) is not int or not 1<=abs(x)<=n for row in clauses for x in row):
        raise ValueError("invalid source variable")
    if not n:
        return 0, [()] if any(not row for row in clauses) else [], []
    gates = [[] for _ in range(n)]
    endpoints = []
    for i, row in enumerate(clauses):
        if not row:
            continue
        endpoints.extend([((i,0),True), ((i,len(row)),False)])
        for j,lit in enumerate(row,1):
            prev,cur = (i,j-1),(i,j)
            bad = int(lit<0)
            g = gates[abs(lit)-1]
            g.append((bad, (prev,False),(cur,True)))
            g.append((bad, (prev,True),(cur,False)))
            g.append((1-bad,(cur,False),(cur,False)))

    count = 0
    physical = []
    selectors = []
    representatives = {}

    def bind(site, signed_state):
        key,positive = signed_state
        # A signed physical literal that evaluates to the logical path-state bit.
        literal = site if positive else -site
        if key in representatives:
            root = representatives[key]
            physical.extend([(-literal,root),(literal,-root)])
        else:
            representatives[key] = literal

    for groups in gates:
        p,q,r = range(count+1,count+4)
        count += 3
        selectors.append((p,q,r))
        if pin_selectors:
            physical.extend([(-p,),(-q,)])
        for idx in range(max(3,len(groups))):
            a,b,e,f,g,c = range(count+1,count+7)
            count += 6
            for triple in ((a,p,e),(b,q,f),(e,r,g),(g,f,c)):
                physical.extend(xor_equivalence(*triple))
            if idx < len(groups):
                mode,left,right=groups[idx]
                bind(a,left)
                bind(b,right)
                physical.append((a,b,-c if mode else c))
            else:
                physical.extend([(a,),(-b,),(a,b,c)])
    for key,wanted in endpoints:
        literal = representatives[key]
        physical.append((literal if wanted else -literal,))
    if any(not row for row in clauses):
        physical.extend([(selectors[0][0],),(-selectors[0][0],)])
    return count,physical,selectors


def decode(word,selectors):
    return sum((sum((word>>(i-1))&1 for i in triple)%2)<<j
               for j,triple in enumerate(selectors))

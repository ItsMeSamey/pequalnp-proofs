"""Independent DIMACS model counting and original DAG evaluation on tiny fixtures."""
from itertools import product


def cnf_count(n,clauses):
    def rec(clauses,values):
        while True:
            reduced = []
            for clause in clauses:
                assert len(clause)<=3
                rest = []
                for lit in clause:
                    assert type(lit) is int and 1 <= abs(lit) <= n
                    if abs(lit) not in values:
                        rest.append(lit)
                    elif values[abs(lit)] == int(lit>0):
                        break
                else:
                    rest = tuple(dict.fromkeys(rest))
                    if not rest:
                        return 0
                    if not any(-lit in rest for lit in rest):
                        reduced.append(rest)
            if not reduced:
                return 1 << (n-len(values))
            clauses = reduced
            unit = next((c[0] for c in clauses if len(c)==1),None)
            if unit is None:
                select = abs(min(clauses,key=len)[0])
                return sum(rec(clauses,dict(values)|{select:b}) for b in (0,1))
            values[abs(unit)] = int(unit>0)
    return rec(clauses,{})


def section():
    from check_binary_fault_solver import Source, raw
    from section_syndrome_cnf import compile_sections, matching_pair_source, branch_cnf
    c = Source(4)
    cut = c.xor(c.xor(1,2),0)
    F = c.finish(c.nand(cut,0))
    obj = compile_sections(4,F,(0,),(((1,2,3),(cut,)),))
    assert obj is not None and obj.width == 2
    for fixed in ((),(0,),(1,)):
        variables,clauses = obj.cnf(fixed)
        total = cnf_count(variables,clauses)
        original = [x for x in range(16) if (not fixed or x>>3 == fixed[0]) and raw(4,F,x)]
        assert total*obj.multiplicity == len(original)
    for y in range(4):
        x = obj.lift(y)
        assert x>>3 == y>>1 and raw(4,F,x) == raw(2,obj.circuit,y)


    n,G,public,sections = matching_pair_source(2)
    paired = compile_sections(n,G,public,sections)
    assert paired is not None
    physical = [x for x in range(1<<n) if raw(n,G,x)]
    reduced = [y for y in range(1<<paired.width) if raw(paired.width,paired.circuit,y)]
    # Two ordered disjoint pairs of 2x2 permutation matrices.
    assert len(physical) == len(reduced)*paired.multiplicity == 2
    for y in reduced:
        x = paired.lift(y)
        assert x in physical
        pins = {i:(y>>(paired.width-i-1))&1 for i in range(paired.width)}
        variables,clauses = branch_cnf(paired,pins)
        assert cnf_count(variables,clauses) == 1


def evaluate(n,gates,out,x):
    w = {-1:0,-2:1,**{i:(x>>(n-1-i))&1 for i in range(n)}}
    for i,g in enumerate(gates,n):
        if g[0] == 'BINARY':
            _,table,a,b = g
            w[i] = (table >> (2*w[a]+w[b])) & 1
        elif g[0] == 'MUX':
            _,s,a,b = g
            w[i] = w[(a,b)[w[s]]]
        elif g[0] == 'PARITY':
            w[i] = (g[1]+sum(w[z] for z in g[2]))%2
        elif g[0] == 'AND':
            w[i] = int(all(w[z] for z in g[1]))
        elif g[0] == 'OR':
            w[i] = int(any(w[z] for z in g[1]))
        else:
            raise AssertionError('unknown raw opcode')
    return w[out]


def check(n,gates,out,all_pins=True):
    from mux_fourier_october import terms,count,solve
    rows = [evaluate(n,gates,out,x) for x in range(1<<n)]
    cases = [()]
    if all_pins:
        cases.extend(tuple(enumerate(bits)) for bits in product((0,1),repeat=n))
    parity = sum(g[0]=='PARITY' for g in gates)
    req = 1 << (1+sum(g[0] in ('AND','OR','PARITY') for g in gates)
                +len({g[1] for g in gates if g[0]=='MUX'}))
    cancellation = False
    for pins in cases:
        models = [x for x,v in enumerate(rows) if v and
                  all(((x>>(n-1-i))&1)==b for i,b in pins)]
        signed = 0
        gross = 0
        for term in terms(n,gates,out,pins=pins):
            assert term.sign in (-1,1)
            tally = cnf_count(term.variables,term.clauses)
            signed += term.sign*tally
            gross += tally
        assert signed == len(models)*(1<<parity)
        cancellation |= gross>abs(signed)
    calls = []
    def oracle(v,c):
        result = cnf_count(v,c)
        calls.append(result)
        return result
    got = count(n,gates,out,oracle)
    assert got['status']=='ok' and got['count']==sum(rows)
    assert got['calls']==len(calls) and got['required']==req
    result = solve(n,gates,out,oracle)
    assert result['status']==('witness' if any(rows) else 'unsat')
    if any(rows):
        assert rows[result['assignment']]
    def forbidden(*_):
        raise AssertionError('called oracle after cap refusal')
    low = count(n,gates,out,forbidden,max_calls=req-1)
    assert low['status']=='unknown' and low['required']==req
    assert solve(n,gates,out,forbidden,max_calls=0)['status']=='unknown'
    return cancellation


def main():
    # With selector 0 fixed, the next selector becomes constant or aliases
    # input 1. Several branches guess an inconsistent exposed selector.
    gates = [('MUX',0,-1,1),('MUX',2,0,-2),('MUX',2,-2,1),
             ('BINARY',6,3,4),('MUX',0,5,4),('MUX',0,6,1)]
    check(2,gates,7)
    check(1,[('MUX',-1,0,-2),('MUX',-2,-1,1)],2)
    check(0,[('AND',()),('OR',()),('PARITY',1,(0,0,1))],2)
    check(0,[],-1)
    check(0,[],-2)
    # On a pinned false output the integer sum may vanish even though both
    # signed parts have physical models.
    seen = [check(2,[(op,(0,1))],2) for op in ('AND','OR')]
    seen.append(check(2,[('PARITY',1,(0,1,1,-2))],2))
    assert any(seen)
    print('Signed raw MUX and dense-gate controls passed.',flush=True)
    section()
    print('Section CNF multiplicity and physical lift passed.',flush=True)


if __name__ == '__main__':
    main()

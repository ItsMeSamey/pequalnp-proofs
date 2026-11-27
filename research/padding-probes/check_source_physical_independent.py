"""Source-SAT controls. The reference enumerator never calls the encoded solver."""
from collections import Counter
from itertools import product
import json
from check_event_tree_native import run_machine, raw_key
from padding_cnf import encode


def truths(n, clauses, pins):
    return {x for x in range(1 << n)
            if all(((x >> (i-1)) & 1) == b for i,b in pins)
            and all(any(((x >> (abs(lit)-1)) & 1) == (lit > 0) for lit in row)
                    for row in clauses)}


def forced(lit, j, k):
    return [(lit, a*j, b*k) for a,b in product((1,-1),repeat=2)]


def check_word(compiled, machine, mask, raw):
    n = compiled.slots_n
    key = raw_key(raw, n)
    assert encode([], n, key) == raw
    assert len(compiled.aliases) == n+1 and key >> n == 1 and n % 6 == 0
    values = {}
    for i,literal in enumerate(compiled.aliases):
        value = ((key >> i) & 1) ^ int(literal < 0)
        assert values.setdefault(abs(literal),value) == value
    for i in range(0,n,6):
        assert ((key >> i) & 7) in (0,7)
        assert ((key >> (i+3)) & 7) != 0
    for var,ids in compiled.occurrences.items():
        if var <= compiled.n:
            assert all(values[name] == ((mask >> (var-1)) & 1) for name in ids)
    assert run_machine(machine,raw)[0] == 1
    assert run_machine(machine,encode([],n,key ^ (1 << n)))[0] == 0
    multiplicity = Counter(abs(a) for a in compiled.aliases[:-1])
    assert max(multiplicity.values(),default=0) <= 2
    if compiled.exact_twice:
        assert all(k == 2 for k in multiplicity.values())
    observed = compiled.lift(raw)
    used = sum(1 << (v-1) for v in compiled.occurrences if 1 <= v <= compiled.n)
    assert observed & used == mask & used


def main():
    from stage6_source_solver import compile_source, fixed_dfa, solve
    machine = fixed_dfa()
    rows = {}
    def case(name,n,clauses,*,pins=(),twice=False,stages=(),limit=0,expect=None):
        allowed = truths(n,clauses,pins)
        answer = solve(n,clauses,exact_twice=twice,source_pins=pins,stages=stages,
                       fallback_limit=limit)
        status = answer['status']
        assert status == (expect or ('SAT' if allowed else 'UNSAT')), (name,answer)
        if status == 'SAT':
            assert answer['witness'] in allowed
            forest = compile_source(n,clauses,exact_twice=twice)
            check_word(forest,machine,answer['witness'],answer['physical'])
        else:
            assert answer.get('witness') is None and answer.get('physical') is None
        if name in ('strict-stage-positive','strict-stage-negative','no-clauses-stage'):
            assert [a['stage'] for a in answer['attempts']] == ['block']
        if name.startswith('coupled-cap'):
            assert answer['attempts'][-1]['examined'] == 15 and answer['attempts'][-1]['total'] == 16
        if name == 'strict-cap-fallback':
            assert answer['attempts'][0]['status'] == 'unknown' and answer['attempts'][-1]['stage']=='source-enumeration'
        rows[name] = status
        return answer

    coupled = forced(1,2,3) + forced(-1,2,4)
    assert not truths(4,coupled,())
    assert all(truths(4,coupled[:i]+coupled[i+1:],()) for i in range(len(coupled)))
    for twice in (False,True):
        suffix = '-two' if twice else '-chain'
        case('coupled'+suffix,4,coupled,twice=twice,limit=16)
        case('coupled-cap'+suffix,4,coupled,twice=twice,limit=15,expect='UNKNOWN')
        case('coupled-repaired'+suffix,5,coupled[:-1],pins=[(5,1)],twice=twice,limit=16)
        case('inactive-and-units'+suffix,6,[(3,),(-2,3)],pins=[(6,1),(2,0)],
             twice=twice,limit=2)
        case('empty-clause'+suffix,2,[()],twice=twice,limit=4)
        case('empty-source'+suffix,3,[],pins=[(3,1)],twice=twice,limit=1)
    case('conflicting-pins',3,[(1,-2,3)],pins=[(3,0),(3,1)])
    physical_stage = [('block', {'backend':'macro','step_cap':None,'state_cap':None})]
    clause = [(1,-2,3)]
    case('strict-stage-positive',4,clause,pins=[(4,1)],stages=physical_stage)
    case('strict-stage-negative',4,clause,pins=[(1,0),(2,1),(3,0),(4,1)],stages=physical_stage)
    capped = [('block',{'backend':'macro','state_cap':0})]
    case('strict-stage-cap',3,clause,stages=capped,expect='UNKNOWN')
    case('strict-cap-fallback',3,clause,stages=capped,limit=8)
    case('no-clauses-stage',0,[],stages=physical_stage)
    for twice in (False,True):
        comp = compile_source(4,clause,exact_twice=twice)
        for mask in truths(4,clause,()):
            check_word(comp,machine,mask,comp.word(mask))
        raw = comp.word(1)
        key = raw_key(raw, comp.slots_n)
        flip = sum(1 << i for i,a in enumerate(comp.aliases) if abs(a)==abs(comp.aliases[0]))
        forged = encode([],comp.slots_n,key ^ flip)
        assert run_machine(machine,forged)[0] == 0
        try:
            comp.lift(forged)
        except ValueError:
            pass
        else:
            raise AssertionError('broken equality accepted in source projection')
        try:
            comp.word(2)
        except ValueError:
            pass
        else:
            raise AssertionError('negative source assignment encoded as a positive witness')
    print(json.dumps(rows,sort_keys=True))


if __name__ == '__main__':
    main()

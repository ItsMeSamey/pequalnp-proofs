"""Rank-greedy semantic pivots for sparse width-three CNF."""
from collections.abc import Mapping
from itertools import product
from source_easy_prepass import _binary


def solve(n, clauses, *, source_pins=(), rank_cap=None, discovery_cap=None, branch_cap=None):
    """Discovery charges feasibility calls, visited vertices/edges and stored candidate records.
    Branches charge one full pivot assignment. Parsing and greedy cover are polynomial.
    """
    if type(n) is not int or n < 0:
        raise ValueError("invalid arity")
    for cap in (rank_cap, discovery_cap, branch_cap):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError("invalid cap")
    original = tuple(tuple(row) for row in clauses)
    if any(len(row)>3 or any(type(x) is not int or not 1<=abs(x)<=n for x in row)
           for row in original):
        raise ValueError("invalid source clause")
    items = source_pins.items() if isinstance(source_pins, Mapping) else source_pins
    pins = tuple(tuple(pair) for pair in items)
    fixed = {}
    conflict = False
    for v, bit in pins:
        if type(v) is not int or not 1<=v<=n or type(bit) is not int or bit not in (0,1):
            raise ValueError("invalid source pin")
        conflict |= v in fixed and fixed[v] != bit
        fixed[v] = bit
    stats = dict(discovery_work=0, projection_calls=0, branch_calls=0, base_binary_rows=0,
                 implication_vertices=0, implication_edges=0, candidate_records=0)
    stats.update(rank_work=0, rank=None, common_rank=None, gains=[], basis_rows=0, ternary_rows=0)
    selected = []

    def result(status, reason=None, true=None):
        return dict(status=status, true_variables=true, pivots=tuple(selected),
                    metrics=stats, reason=reason)

    if conflict:
        return result("UNSAT")
    residual = set()
    for row in original:
        lits = set(row)
        if any(-x in lits or fixed.get(abs(x)) == int(x>0) for x in lits):
            continue
        live = tuple(sorted(x for x in lits if abs(x) not in fixed))
        if not live:
            return result("UNSAT")
        residual.add(live)
    binary = tuple(sorted(r for r in residual if len(r)<=2))
    triples = tuple(sorted(r for r in residual if len(r)==3))

    stats["ternary_rows"] = len(triples)

    class Cutoff(Exception):
        pass

    def charge():
        if discovery_cap is not None and stats['discovery_work'] >= discovery_cap:
            raise Cutoff
        stats['discovery_work'] += 1

    def feasible(units):
        charge()
        stats['projection_calls'] += 1
        return _binary(binary + tuple((x,) for x in units)) is not None

    graph = {}
    for row in binary:
        a,b = row[0],row[-1]
        graph.setdefault(-a, []).append(b)
        graph.setdefault(-b, []).append(a)

    def consequences(units):
        # Fixed backbone facts need not be added: they cannot have a
        # feasible opposite singleton. All varying forced literals are
        # reachable from one of the three pins in the implication graph.
        seen = set(units)
        stack = list(units)
        while stack:
            charge()
            stats['implication_vertices'] += 1
            x = stack.pop()
            for y in graph.get(x, ()):
                charge()
                stats['implication_edges'] += 1
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return seen

    covers = {}
    pending = set()
    common = {}
    try:
        charge()
        stats["projection_calls"] += 1
        root = _binary(binary)
        if root is None:
            return result("UNSAT")
        for i,row in enumerate(triples):
            singletons = []
            for j in range(3):
                units = tuple(x if k == j else -x for k,x in enumerate(row))
                if not feasible(units):
                    common[i] = row[:j]+row[j+1:]
                    break
                singletons.append(units)
            else:
                pending.add(i)
                forces = {}
                for j,units in enumerate(singletons):
                    for lit in consequences(units):
                        forces.setdefault(lit, j)
                for w,j in forces.items():
                    if w > 0 and -w in forces:
                        charge()
                        stats['candidate_records'] += 1
                        k = forces[-w]
                        # When w=0, the singleton forcing +w is missing.
                        # When w=1, use the singleton forcing -w instead.
                        halves = row[:j]+row[j+1:], row[:k]+row[k+1:]
                        covers.setdefault(w, {})[i] = halves
        stats['base_binary_rows'] = len(common)
    except Cutoff:
        return result("UNKNOWN", "discovery cap")

    def rank_charge(amount=1):
        if rank_cap is not None and amount > rank_cap-stats["rank_work"]:
            raise Cutoff
        stats["rank_work"] += amount

    # A monomial in root-relative flip bits indicates a principal upper
    # set. Find its least flip set by walking the seeded implication SCCs.
    # Distinct least flip sets give independent columns by triangularity.
    form_ids = {}
    closure_cache = {}
    def column(seeds):
        rank_charge(1+len(seeds))
        if seeds in closure_cache:
            return closure_cache[seeds]
        todo = [(-v if root.get(v,0) else v) for v in seeds]
        seen = set(todo)
        consistent = True
        while todo and consistent:
            rank_charge()
            x = todo.pop()
            for y in graph.get(x, ()):
                rank_charge()
                if -y in seen:
                    consistent = False
                    break
                if y not in seen:
                    seen.add(y)
                    todo.append(y)
        ident = None
        if consistent:
            rank_charge(1+len(seen))
            least = frozenset(abs(x) for x in seen if root.get(abs(x),0) != int(x>0))
            ident = form_ids.setdefault(least, len(form_ids))
        closure_cache[seeds] = ident
        return ident

    def failure_vector(row):
        terms = [()]
        for x in row:
            # A literal true at the root fails on a flip; one false there
            # fails on (1 + flip) in GF(2).
            rank_charge(1+2*len(terms))
            enlarged = [t+(abs(x),) for t in terms]
            if root.get(abs(x),0) == int(x>0):
                terms = enlarged
            else:
                terms.extend(enlarged)
        values = set()
        for t in terms:
            j = column(tuple(sorted(t)))
            if j is not None:
                if j in values:
                    values.remove(j)
                else:
                    values.add(j)
        return values

    def insert(basis, row):
        while row:
            rank_charge(1+len(row))
            lead = max(row)
            if lead not in basis:
                basis[lead] = row
                return True
            rank_charge(1+len(row)+len(basis[lead]))
            row = row ^ basis[lead]
        return False

    owned = {}
    try:
        vectors = [failure_vector(row) for row in triples]
        full = {}
        for vector in vectors:
            rank_charge()
            insert(full, vector)
        target = stats['rank'] = len(full)
        stats['closure_columns'] = len(form_ids)
        basis = {}
        common_rows = []
        for i,reduced in common.items():
            rank_charge()
            if insert(basis, vectors[i]):
                common_rows.append(reduced)
        stats['common_rank'] = len(basis)
        while len(basis) < target:
            gain = 0
            winner = None
            for w,pieces in covers.items():
                rank_charge(1+len(basis))
                trial = basis.copy()
                kept = []
                for i in pieces:
                    rank_charge()
                    if insert(trial, vectors[i]):
                        kept.append(i)
                if len(kept)>gain or (gain and len(kept)==gain and w<winner):
                    winner, gain, best, hits = w, len(kept), trial, kept
            if not gain:
                raise ArithmeticError("no rank-increasing source pivot")
            basis = best
            selected.append(winner)
            stats['gains'].append(gain)
            owned[winner] = [covers[winner][i] for i in hits]
        stats['basis_rows'] = len(basis)
    except Cutoff:
        return result("UNKNOWN", "rank cap")

    for bits in product((0, 1), repeat=len(selected)):
        if branch_cap is not None and stats['branch_calls'] >= branch_cap:
            return result("UNKNOWN", "branch cap")
        stats['branch_calls'] += 1
        rows = list(binary) + common_rows
        for w, bit in zip(selected, bits):
            rows.append((w if bit else -w,))
            rows.extend(halves[bit] for halves in owned[w])
        model = _binary(rows)
        if model is None:
            continue
        true = tuple(sorted(v for v, bit in (fixed | model).items() if bit))
        ids = set(true)
        if (any(not any((abs(x) in ids)==(x>0) for x in row) for row in original)
                or any(int(v in ids)!=bit for v,bit in pins)):
            raise ArithmeticError("invalid original source witness")
        return result("SAT", true=true)
    return result("UNSAT")

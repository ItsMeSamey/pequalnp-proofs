"""Source-checked local simplification for the signed CNF commutator compiler."""
from barrington_cnf_rail import IDENT,RHO,_compile,_tree
from cnf_restriction_cache import RestrictionCache,replay_unsat


def source_tree(n,clauses):
    rows=tuple(tuple(c) for c in clauses)
    if type(n) is not int or n<0 or any(type(x) is not int or not 1<=abs(x)<=n for c in rows for x in c):
        raise ValueError("invalid source")
    if any(not c for c in rows):
        return False
    if not rows:
        return True
    return _tree([_tree([(0,x) for x in c],"or") for c in rows],"and")[1]


def _clause(node):
    if type(node) is int:
        return (node,)
    if type(node) is tuple and node[0]=="or":
        a,b=_clause(node[1]),_clause(node[2])
        if a is not None and b is not None:
            return a+b
    return None


def _conjuncts(node):
    if type(node) is tuple and node[0]=="and":
        yield from _conjuncts(node[1])
        yield from _conjuncts(node[2])
    else:
        clause=_clause(node)
        if clause is not None:
            yield clause


def propose(n,clauses,width_limit=4):
    """Small-core heuristic. Each hint names an actual source subtree path."""
    hints={}
    cache=RestrictionCache()
    def visit(node,path):
        if type(node) is not tuple:
            return
        if node[0]=="and":
            groups={}
            for clause in _conjuncts(node):
                scope=frozenset(map(abs,clause))
                if len(scope)<=width_limit:
                    groups.setdefault(scope,set()).add(tuple(sorted(set(clause))))
            for scope,rows in groups.items():
                if len(rows)<2:
                    continue
                # Each non-tautological full-support clause excludes just one word.
                if len(rows)<1<<len(scope):
                    continue
                rows=tuple(sorted(rows))
                cert=cache.certificate(n,rows)
                if cert is not None:
                    hints[path]=(rows,cert)
                    return
        visit(node[1],path+(0,))
        visit(node[2],path+(1,))
    visit(source_tree(n,clauses),())
    return hints


def simplify(n,clauses,hints):
    """Verify all hints on their original input subtree or raise ValueError."""
    clauses=tuple(tuple(c) for c in clauses)
    tree=source_tree(n,clauses)
    by_path={}
    for path,hint in hints.items():
        if hint and hint[0]=="interface-unsat":
            if not verify_interface(n,clauses,path,hint):
                raise ValueError("invalid shared-interface refutation")
            by_path[path]=False
            continue
        rows,cert=hint
        node=tree
        for side in path:
            if type(node) is not tuple or type(side) is not int or side not in (0,1):
                raise ValueError("invalid subtree path")
            node=node[1+side]
        actual={tuple(sorted(set(c))) for c in _conjuncts(node)}
        if any(tuple(sorted(set(c))) not in actual for c in rows) or not replay_unsat(rows,{},cert):
            raise ValueError("invalid contradiction at named subtree")
        by_path[path]=False
    def visit(node,path):
        if path in by_path:
            return by_path[path]
        if type(node) is not tuple:
            return node
        op,left,right=node
        a,b=visit(left,path+(0,)),visit(right,path+(1,))
        if type(a) is bool:
            return (b if a else False) if op=="and" else (True if a else b)
        if type(b) is bool:
            return (a if b else False) if op=="and" else (True if b else a)
        if a==b:
            return a
        if type(a) is int and type(b) is int and a==-b:
            return op=="or"
        return op,a,b
    return visit(tree,())


def compile_verified(n,clauses,hints):
    simplified=simplify(n,clauses,hints)
    if type(simplified) is bool:
        return [],RHO if simplified else IDENT
    return _compile(simplified,RHO),IDENT


def _interface_parts(tree,path):
    node=tree
    for side in path:
        if type(node) is not tuple or type(side) is not int or side not in (0,1):
            raise ValueError("invalid interface path")
        node=node[1+side]
    if type(node) is not tuple or node[0]!="and":
        raise ValueError("expected a source conjunction")
    def clauses(part):
        if type(part) is tuple and part[0]=="and":
            return clauses(part[1])+clauses(part[2])
        clause=_clause(part)
        if clause is None:
            raise ValueError("child is not a conjunction of clauses")
        return (clause,)
    sides=tuple(clauses(x) for x in node[1:])
    scopes=[{abs(x) for c in rows for x in c} for rows in sides]
    return sides,sorted(scopes[0]&scopes[1])


def prove_interface(n,clauses,path=()):
    """Return an UNSAT proof or an original-variable witness for the named AND."""
    sides,shared=_interface_parts(source_tree(n,clauses),path)
    cache=RestrictionCache()
    cases=[]
    for word in range(1<<len(shared)):
        pins={v:(word>>i)&1 for i,v in enumerate(shared)}
        witnesses=[]
        for side,rows in enumerate(sides):
            witness,_=cache.query(n,rows,pins)
            if witness is None:
                cases.append((side,cache.certificate(n,rows,pins)))
                break
            witnesses.append(witness)
        else:
            # Unassigned off-child bits of the cache witnesses default to zero.
            # Explicitly project onto each child's scope before merging.
            merged=0
            for rows,witness in zip(sides,witnesses):
                scope={abs(x) for c in rows for x in c}
                merged |= witness & sum(1<<(v-1) for v in scope)
            return "sat",merged
    return "interface-unsat",tuple(cases)


def verify_interface(n,clauses,path,certificate):
    """Return Boolean validity. A SAT claim is local to the named subtree."""
    try:
        sides,shared=_interface_parts(source_tree(n,clauses),path)
        kind,payload=certificate
        if kind=="sat":
            return type(payload) is int and 0<=payload and payload.bit_length()<=n and all(
                any(bool(payload&(1<<(abs(x)-1)))==(x>0) for x in c) for rows in sides for c in rows)
        if kind!="interface-unsat" or len(payload)!=1<<len(shared):
            return False
        for word,(side,proof) in enumerate(payload):
            if type(side) is not int or side not in (0,1):
                return False
            pins={v:(word>>i)&1 for i,v in enumerate(shared)}
            if not replay_unsat(sides[side],pins,proof):
                return False
        return True
    except (ValueError,TypeError,IndexError):
        return False

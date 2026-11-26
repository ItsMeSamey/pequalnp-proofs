"""Exact CNF restriction cache. Signed literals use one-based variable numbers."""
from itertools import permutations, product


def normalize(rows):
    clauses = set()
    for clause in rows:
        lits = frozenset(clause)
        if any(-x in lits for x in lits):
            continue
        if not lits:
            return ((),)
        clauses.add(tuple(sorted(lits)))
    return tuple(sorted(clauses))


def restrict(rows, values):
    return normalize([lit for lit in row if abs(lit) not in values]
                     for row in rows if not any(values.get(abs(lit)) == (lit>0)
                                               for lit in row if abs(lit) in values))


def canonical(rows):
    """Return least signed-renaming image and input coordinates for its literals."""
    variables = sorted({abs(x) for row in rows for x in row})
    best = lift = None
    for order in permutations(variables):
        for signs in product((1,-1),repeat=len(order)):
            inverse = tuple(v*s for v,s in zip(order,signs))
            forward = {v:(i+1)*s for i,(v,s) in enumerate(zip(order,signs))}
            key = tuple(sorted(tuple(sorted(forward[abs(x)]*(1 if x>0 else -1)
                                            for x in row)) for row in rows))
            if best is None or key<best:
                best,lift = key,inverse
    return best,lift


def _lift(mask, inverse):
    return {abs(lit): bool(mask>>i&1) ^ (lit<0) for i,lit in enumerate(inverse)}


class RestrictionCache:
    """SAT entries carry witness bits; UNSAT entries carry replayable split proofs."""
    def __init__(self):
        self.sat = {}
        self.unsat = {}

    def _solve(self, key):
        if key in self.sat:
            return self.sat[key]
        if key in self.unsat:
            return None
        if key == ((),):
            self.unsat[key] = ()
            return None
        if not key:
            self.sat[key] = 0
            return 0
        variable = min(map(abs,key[0]))
        children = []
        for value in (False,True):
            child, inverse = canonical(restrict(key,{variable:value}))
            children.append((child,inverse))
            witness = self._solve(child)
            if witness is not None:
                values = _lift(witness,inverse)
                values[variable] = value
                result = sum(1<<(i-1) for i,bit in values.items() if bit)
                self.sat[key] = result
                return result
        self.unsat[key] = (variable,*children)
        return None

    def query(self,n,rows,pins=None):
        """Return (original-coordinate witness or None, canonical residual root)."""
        rows = tuple(tuple(row) for row in rows)
        pins = {} if pins is None else dict(pins)
        if not isinstance(n,int) or n<0 or any(not isinstance(x,int) or not 1<=abs(x)<=n
                                              for row in rows for x in row):
            raise ValueError("invalid original coordinates")
        if any(not isinstance(v,int) or not 1<=v<=n or b not in (0,1) for v,b in pins.items()):
            raise ValueError("invalid pinned coordinate")
        key,inverse = canonical(restrict(normalize(rows),pins))
        witness = self._solve(key)
        if witness is None:
            return None,key
        values = _lift(witness,inverse)
        values.update(pins)
        return sum(1<<(i-1) for i,bit in values.items() if bit),key


    def certificate(self,n,rows,pins=None):
        """Return (root key, root inverse signed permutation, reachable DAG)."""
        rows = tuple(tuple(clause) for clause in rows)
        pins = {} if pins is None else dict(pins)
        witness,root = self.query(n,rows,pins)
        if witness is not None:
            return None
        _,inverse = canonical(restrict(normalize(rows),pins))
        graph = {}
        stack = [root]
        while stack:
            key = stack.pop()
            if key in graph:
                continue
            node = self.unsat[key]
            graph[key] = node
            stack.extend(child for child,label in node[1:])
        return root,inverse,graph


def _labeled_image(rows,label):
    """Apply an advertised inverse signed bijection in polynomial time."""
    active = {abs(x) for clause in rows for x in clause}
    if not isinstance(label,tuple) or len(label)!=len(active):
        return None
    if any(type(x) is not int or not x for x in label) or {abs(x) for x in label}!=active:
        return None
    forward = {abs(x): (i+1 if x>0 else -(i+1)) for i,x in enumerate(label)}
    return tuple(sorted(tuple(sorted(forward[abs(x)]*(1 if x>0 else -1)
                                     for x in clause)) for clause in rows))


def replay_unsat(rows,pins,certificate):
    """Verify a labeled branching DAG with no signed-canonicalization search."""
    if not isinstance(certificate,tuple) or len(certificate)!=3:
        return False
    root,label,proof = certificate
    if not isinstance(proof,dict) or _labeled_image(restrict(normalize(rows),pins),label)!=root:
        return False
    pending = [root]
    checked = set()
    while pending:
        key = pending.pop()
        if not isinstance(key,tuple) or any(not isinstance(row,tuple) or
            any(type(x) is not int or not x for x in row) for row in key):
            return False
        if key in checked:
            continue
        checked.add(key)
        node = proof.get(key)
        if key == ((),):
            if node != ():
                return False
            continue
        if not isinstance(node,tuple) or len(node)!=3:
            return False
        v = node[0]
        if type(v) is not int or not any(abs(x)==v for row in key for x in row):
            return False
        for value,edge in enumerate(node[1:]):
            if not isinstance(edge,tuple) or len(edge)!=2:
                return False
            child,edge_label = edge
            image = _labeled_image(restrict(key,{v:value}),edge_label)
            if image is None or image!=child:
                return False
            pending.append(child)
    return True

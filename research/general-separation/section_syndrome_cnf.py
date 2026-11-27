"""Certified chronological multi-output cuts of an original ordered NAND DAG.

compile_sections(n,F,public,sections) takes public input indices and ordered
(bank input indices, cut output wire IDs) pairs. None means certificate declined.
Coordinates use wire 0 as MSB, gate i uses wire n+i, and -1/-2 are 0/1.
"""
from dataclasses import dataclass

from pivot_cone_rewrite import _xor
from primitive_rewrite_chain import _inputs, evaluate
from quadratic_polar_online import _space


@dataclass(frozen=True)
class Compiled:
    n: int
    original: tuple
    public: tuple
    sections: tuple  # (bank, independent (cut wire, local slope) pairs)
    width: int
    circuit: tuple

    @property
    def multiplicity(self):
        return 1 << (self.n-self.width)

    def lift(self, word):
        """Choose free Gaussian coordinates zero and return one original preimage."""
        if type(word) is not int or not 0 <= word < 1 << self.width:
            raise ValueError('quotient word out of range')
        def bit(i):
            return (word >> (self.width-i-1)) & 1
        raw = sum(bit(j) << (self.n-i-1) for j, i in enumerate(self.public))
        pos = len(self.public)
        gates, out = self.original
        for bank, independent in self.sections:
            rows = []
            for cut, slope in independent:
                offset = evaluate(self.n, gates, cut, raw)
                rows.append((slope, bit(pos) ^ offset))
                pos += 1
            x = _space(len(bank), rows)[0]
            for j, i in enumerate(bank):
                raw |= ((x >> j) & 1) << (self.n-i-1)
        if evaluate(self.n, gates, out, raw) != evaluate(self.width, *self.circuit, word):
            raise AssertionError('section lift failed original NAND evaluation')
        return raw

    def cnf(self, public_prefix=()):
        """Exact Tseitin leaf after guessing a prefix of the listed public bits.

        Result is (declared variable count, tuple of clauses). A DIMACS literal
        is a signed one-based variable. Unused quotient inputs remain declared.
        """
        prefix = tuple(public_prefix)
        if len(prefix) > len(self.public) or any(type(x) is not int or x not in (0,1) for x in prefix):
            raise ValueError('invalid public prefix')
        gates, out = self.circuit
        k = len(prefix)
        variables = self.width-k+len(gates)
        def wire(w, positive=True):
            if w < 0 or w < k:
                value = (-1-w if w < 0 else prefix[w]) == 1
                return value if positive else not value
            return (w-k+1) * (1 if positive else -1)
        clauses = []
        def clause(*ls):
            if any(l is True for l in ls):
                return
            clauses.append(tuple(l for l in ls if l is not False))
        for w, (a,b) in enumerate(gates, self.width):
            clause(wire(a,False),wire(b,False),wire(w,False))
            clause(wire(a),wire(w))
            clause(wire(b),wire(w))
        clause(wire(out))
        return variables, tuple(clauses)


def compile_sections(n, F, public, sections):
    gates, out = F
    gates = _inputs(n, gates, out)
    public = tuple(public)
    sections = tuple((tuple(bank),tuple(cuts)) for bank,cuts in sections)
    inputs = public + tuple(i for bank,_ in sections for i in bank)
    if any(type(i) is not int for i in inputs) or sorted(inputs) != list(range(n)):
        raise ValueError('public and bank coordinates must partition original inputs')
    cuts = [w for _, cones in sections for w in cones]
    if any(type(w) is not int or not 0 <= w < n+len(gates) for w in cuts) or len(set(cuts)) != len(cuts):
        raise ValueError('invalid or duplicate cut wire')

    # Symbolic quotient wire IDs are tagged, since its input count is unknown yet.
    reduced = []
    def nand(a,b):
        result = ('g',len(reduced))
        reduced.append((a,b))
        return result
    def xor(a,b):
        if a == -1:
            return b
        middle = nand(a,b)
        return nand(nand(a,middle),nand(b,middle))
    mapped = {-1:-1,-2:-2}
    mapped.update((i,('x',j)) for j,i in enumerate(public))
    width = len(public)
    past = set(public)
    charts = []

    for bank, outputs in sections:
        if any(w in mapped for w in outputs):
            return None
        local = {w:j for j,w in enumerate(bank)}
        visible_before = dict(mapped)
        # Offset bit 0 is the constant 1. Offset bit w+1 names an ORIGINAL
        # wire independent of this bank; only visible names may survive in
        # the consistency relation of a dependent cut.
        profile = {-1:(0,0),-2:(0,1)}
        for i in range(n):
            if i in local:
                profile[i] = (1 << local[i],0)
            elif i in past:
                profile[i] = (0,1 << (i+1))
        for w,(a,b) in enumerate(gates,n):
            if w in visible_before:
                profile[w] = (0,1 << (w+1))
            elif a == b and a in profile:
                slope, offset = profile[a]
                profile[w] = slope, offset ^ 1
            else:
                pair = _xor(n,gates,a,b)
                if pair is not None and all(v in profile for v in pair):
                    (s,f),(t,g) = (profile[v] for v in pair)
                    profile[w] = s ^ t, f ^ g
                elif a in profile and b in profile and not (profile[a][0] or profile[b][0]):
                    profile[w] = 0,1 << (w+1)
        pivots = {}
        independent = []
        for w in outputs:
            if w not in profile:
                return None
            slope, offset = profile[w]
            coeff = 0
            while slope:
                p = slope.bit_length()-1
                if p not in pivots:
                    j = len(independent)
                    pivots[p] = slope, offset, coeff ^ (1 << j)
                    independent.append((w,profile[w][0]))
                    mapped[w] = ('x',width)
                    width += 1
                    break
                a,b,c = pivots[p]
                slope,offset,coeff = slope^a,offset^b,coeff^c
            else:
                value = -1
                for j,(v,_) in enumerate(independent):
                    if coeff & (1 << j):
                        value = xor(value,mapped[v])
                tokens = offset >> 1
                while tokens:
                    low = tokens & -tokens
                    token = low.bit_length()-1
                    if token not in visible_before:
                        return None
                    value = xor(value,visible_before[token])
                    tokens ^= low
                mapped[w] = nand(value,value) if offset & 1 else value
        charts.append((bank,tuple(independent)))
        past.update(bank)

    live = set()
    stack = [out]
    while stack:
        w = stack.pop()
        if w in mapped or w in live:
            continue
        if w < n:
            return None
        live.add(w)
        stack.extend(gates[w-n])
    for w in sorted(live):
        a,b = gates[w-n]
        mapped[w] = nand(mapped[a],mapped[b])
    def address(token):
        if type(token) is int:
            return token
        kind,j = token
        return j if kind == 'x' else width+j
    circuit = tuple((address(a),address(b)) for a,b in reduced),address(mapped[out])
    return Compiled(n,(gates,out),public,tuple(charts),width,circuit)


def branch_cnf(model, guesses):
    """Guess any quotient input/gate values; certify each guessed producer.

    guesses maps quotient wire IDs to bits. Return a parsimonious 3CNF leaf,
    including density padding if needed. All original multiplicity is external.
    """
    gates,out = model.circuit
    guesses = dict(guesses)
    if any(type(w) is not int or not 0 <= w < model.width+len(gates) or
           type(b) is not int or b not in (0,1) for w,b in guesses.items()):
        raise ValueError('invalid guessed wire')
    labels = {-1:False,-2:True}
    clauses = []
    variables = 0
    def neg(a):
        return not a if type(a) is bool else -a
    def clause(*lits):
        if not any(v is True for v in lits):
            clauses.append(tuple(v for v in lits if v is not False))
    for w in range(model.width):
        if w in guesses:
            labels[w] = bool(guesses[w])
        else:
            variables += 1
            labels[w] = variables
    for w,(a,b) in enumerate(gates,model.width):
        u,v = labels[a],labels[b]
        if w in guesses:
            target = bool(guesses[w])
            if target:
                clause(neg(u),neg(v))
            else:
                clause(u)
                clause(v)
            labels[w] = target
        elif u is False or v is False:
            labels[w] = True
        elif u is True:
            labels[w] = neg(v)
        elif v is True or u == v:
            labels[w] = neg(u)
        elif u == -v:
            labels[w] = True
        else:
            variables += 1
            labels[w] = variables
            clause(neg(u),neg(v),-variables)
            clause(u,variables)
            clause(v,variables)
    clause(labels[out])
    while len(clauses) > 5*variables:
        variables += 1
        clauses.append((-variables,))
    return variables, tuple(clauses)


def matching_pair_source(d):
    """Two disjoint permutation matrices through chronological 3-output sections.

    Returns (n,F,public,sections). This builds raw NAND data; it does not solve it.
    """
    if type(d) is not int or d < 1:
        raise ValueError('positive matrix order required')
    size = d*d
    n = 2*size
    gates = []
    def nand(a,b):
        gates.append((a,b))
        return n+len(gates)-1
    def inv(a):
        return nand(a,a)
    def both(a,b):
        return inv(nand(a,b))
    def either(a,b):
        return nand(inv(a),inv(b))
    def xor(a,b):
        middle = nand(a,b)
        return nand(nand(a,middle),nand(b,middle))
    sections, xa, xb = [], [], []
    good = -2
    for i in range(size):
        a,b = 2*i,2*i+1
        ga,gb = -2,-2
        for j in range(max(0,i-size.bit_length()),i):
            ga = nand(ga,2*j)
            gb = nand(gb,2*j+1)
        x,y = xor(a,ga),xor(b,gb)
        z = xor(xor(a,b),xor(ga,gb))
        sections.append(((a,b),(x,y,z)))
        xa.append(x)
        xb.append(y)
        good = both(good,inv(xor(either(x,y),z)))
    for matrix in (xa,xb):
        groups = [matrix[i*d:(i+1)*d] for i in range(d)]
        groups.extend(matrix[i::d] for i in range(d))
        for group in groups:
            seen = -1
            for value in group:
                good = both(good,nand(seen,value))
                seen = either(seen,value)
            good = both(good,seen)
    return n,(tuple(gates),good),(),tuple(sections)

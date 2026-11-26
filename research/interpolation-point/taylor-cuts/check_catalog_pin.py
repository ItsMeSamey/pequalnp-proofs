"""Build a connected exact-3, max-occurrence-4 pin-catalog obstruction."""
from collections import Counter
from itertools import product

class Formula:
    def __init__(self):
        self.n = 0
        self.clauses = []
        self.plant = {}
    def var(self, value=True):
        self.n += 1
        self.plant[self.n] = value
        return self.n
    def force_false(self):
        # Tovey 1984 Thm 2.3, set y=false by literal flip.
        y = self.var(False)
        ds = []
        for _ in range(3):
            a, b, d = self.var(False), self.var(False), self.var(False)
            self.clauses.extend([(-y,a,b),(d,-a,-b),(d,-a,b),(d,a,-b)])
            ds.append(-d)
        self.clauses.append(tuple(ds))
        return y
    def neutral(self, lit):
        a, b = self.var(), self.var()
        self.clauses.append((lit,a,b))
        return a
    def forced_clause(self, lit):
        self.clauses.append((lit,self.force_false(),self.force_false()))

def build():
    F = Formula()
    signs = [1,1,-1]
    anchors = []
    # Target mixed COPY, plus one two-sided test fixture for every native type.
    x = F.var()
    anchors.append([F.neutral(x*s) for s in signs][0])
    for i,sign in enumerate(signs):
        # Variable-side bad pin, closed by a neutral clause at the prescribed port.
        x = F.var(sign < 0)
        opposite = next(j for j,s in enumerate(signs) if s == -sign)
        for j,s in enumerate(signs):
            if j == opposite: F.forced_clause(s*x)
            else:
                a = F.neutral(s*x)
                if i == j: anchors.append(a)
        # Clause-side favorable pin, with neutral variable-side closure at the same type.
        x = F.var(sign > 0)
        for j,s in enumerate(signs):
            if i == j: F.forced_clause(s*x)
            else:
                a = F.neutral(s*x)
                if j == (i+1)%3: anchors.append(a)
    for a,b in zip(anchors,anchors[1:]):
        F.clauses.append((a,b,F.var()))
    return F

def main():
    T = Formula(); y = T.force_false()
    counts = [0,0]
    for vals in product([False, True],repeat=T.n):
        if all(any(vals[abs(z)-1] == (z>0) for z in c) for c in T.clauses):
            counts[vals[y-1]] += 1
    assert counts == [61,0]
    F = build()
    occ = Counter(abs(z) for c in F.clauses for z in c)
    assert max(occ.values()) <= 4
    assert all(len(set(map(abs,c)))==3 for c in F.clauses)
    assert all(any(F.plant[abs(z)] == (z>0) for z in c) for c in F.clauses)
    seen = {1}
    while True:
        reach = set(seen)
        for c in F.clauses:
            vs = set(map(abs,c))
            if vs & seen: reach.update(vs)
        if seen == reach: break
        seen = reach
    assert len(seen)==F.n
    print('forced pin counts',counts,'connected control',F.n,len(F.clauses),'maxocc',max(occ.values()))

if __name__ == '__main__':main()

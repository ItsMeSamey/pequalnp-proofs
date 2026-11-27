"""Degree-three homogeneous consequences of full-support GF(3) equations."""
from dataclasses import dataclass
from itertools import combinations, product


def remainder(row, basis):
    row = list(row)
    for p in sorted(basis):
        c = row[p]
        if c:
            row = [(x-c*y)%3 for x,y in zip(row,basis[p])]
    return tuple(row)


def add(row, basis):
    residual = remainder(row,basis)
    if any(residual):
        p = next(i for i,c in enumerate(residual) if c)
        basis[p] = tuple(c*residual[p]%3 for c in residual)
    return residual


@dataclass
class Quotient:
    n: int
    local: tuple
    global_rows: tuple
    coordinates: tuple
    original: tuple

    def lift(self, signs):
        signs = tuple(signs)
        if len(signs)!=self.n or any(x not in (1,2) for x in signs):
            raise ValueError('invalid full-support quotient assignment')
        full = tuple(c*signs[i]%3 for i,c in self.coordinates)
        if any(sum(x*y for x,y in zip(row,full))%3 for row in self.original):
            raise ValueError('assignment violates original system')
        return full


def close(n, local_rows, global_rows=()):
    """Return an equivalent quotient, or None for a proved contradiction."""
    local, glob = [tuple(tuple(x%3 for x in row) for row in rows)
                   for rows in (local_rows,global_rows)]
    orig = local+glob
    if n<0 or any(len(row)!=n for row in orig):
        raise ValueError('invalid dimensions')
    coords = tuple((i,1) for i in range(n))
    while True:
        basis = {}
        for row in local+glob:
            add(row,basis)
        # Linearity of reduction identifies the syndrome of each unit vector.
        synd = [remainder((int(i==j) for j in range(n)),basis) for i in range(n)]
        if any(not any(s) for s in synd):
            return None
        parent = list(range(n))
        mult = [1]*n
        def find(i):
            m = 1
            while parent[i]!=i:
                m = m*mult[i]%3
                i = parent[i]
            return i,m
        def link(i,j,c):
            # Enforce x_j=c*x_i, including existing links from this pass.
            a,s = find(i)
            b,t = find(j)
            ratio = c*s*t%3
            if a==b:
                return ratio==1
            parent[b],mult[b] = a,ratio
            return True
        lookup = {}
        for i,s in enumerate(synd):
            lookup.setdefault(s,[]).append(i)
        for i,s in enumerate(synd):
            for c in (1,2):
                for j in lookup.get(tuple(-c*t%3 for t in s),()):
                    if j>i and not link(i,j,-c):
                        return None
        for i,j in combinations(range(n),2):
            for c,d in product((1,2),repeat=2):
                want = tuple(-d*(u+c*v)%3 for u,v in zip(synd[i],synd[j]))
                for k in lookup.get(want,()):
                    if k>j and (not link(i,j,c) or not link(i,k,d)):
                        return None
        reps = list(dict.fromkeys(find(i)[0] for i in range(n)))
        if len(reps)==n:
            break
        ids = {r:j for j,r in enumerate(reps)}
        mapping = [(ids[r],c) for r,c in map(find,range(n))]
        def project(row):
            out = [0]*len(ids)
            for x,(i,c) in zip(row,mapping):
                out[i]=(out[i]+x*c)%3
            return tuple(out)
        local,glob = tuple(map(project,local)),tuple(map(project,glob))
        coords = tuple((mapping[i][0],c*mapping[i][1]%3) for i,c in coords)
        n = len(ids)
    # Keep submitted local supports. The global residuals extend their span.
    basis = {}
    loc = []
    for row in local:
        if any(add(row,basis)):
            loc.append(row)
    out = []
    for row in glob:
        residual = add(row,basis)
        if any(residual):
            out.append(residual if sum(map(bool,residual))<sum(map(bool,row)) else row)
    return Quotient(n,tuple(loc),tuple(out),coords,orig)

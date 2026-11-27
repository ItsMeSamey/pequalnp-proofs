"""Portable necessary ordered-region conditions on a monotone operand."""
import itertools


def encode_ordered(highs, lows, n, regions):
    """Return clauses and semantic-key-to-DIMACS-ID map; bit i is feature i."""
    if n < 1 or regions < 1:
        raise ValueError("expected positive feature and region counts")
    highs=sorted(set(highs))
    lows=sorted(set(lows))
    if any(type(x) is not int or not 0<=x<1<<n for x in highs+lows):
        raise ValueError("care row outside feature range")
    names = {}
    clauses = []
    def var(*key):
        return names.setdefault(key,len(names)+1)
    for i in range(n):
        clauses.append([var('color',i,t) for t in range(regions)])
    for i,j in itertools.combinations(range(n),2):
        for t in range(regions):
            clauses.append([-var('color',i,t),-var('color',j,t),var('same',i,j)])
    for h in highs:
        for l in lows:
            diff = [i for i in range(n) if (h & ~l) >> i & 1]
            clauses.append([var('pos',h,i) for i in diff])
            clauses.append([var('neg',l,i) for i in diff])
            for t in range(regions-1):
                clauses.append([-var('true',h,t),-var('false',l,t)]
                               + [var('color',i,k) for i in diff for k in range(t+1)])
            for i,j in itertools.combinations(diff,2):
                clauses.append([-var('pos',h,i),-var('pos',h,j),-var('neg',l,i),
                                -var('neg',l,j),-var('same',i,j)])
    for i in range(n):
        for j,k in itertools.combinations(range(regions),2):
            clauses.append([-var('color',i,j),-var('color',i,k)])
        for t in range(regions-1):
            for h in highs:
                if h >> i & 1:
                    clauses.append([-var('pos',h,i),-var('color',i,t),var('true',h,t)])
            for l in lows:
                if not l >> i & 1:
                    clauses.append([-var('neg',l,i),-var('color',i,t),var('false',l,t)])
    return clauses,names

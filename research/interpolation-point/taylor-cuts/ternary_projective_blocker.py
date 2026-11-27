"""Find a minimal homogeneous ternary hyperplane cover of bounded normal rank."""
from itertools import combinations, product


def projectivize(v):
    v = tuple(a % 3 for a in v)
    t = next((a for a in v if a), 0)
    return tuple(t*a % 3 for a in v)


def find_blocker(normals, rank_cap=3):
    """Return input row indices, basis, and private evaluation words, or None.

    Each private word specifies evaluations on exactly the basis rows as
    projectively normalized. Its zero set in the certificate is its own row.
    """
    normals = [projectivize(v) for v in normals]
    if not normals:
        return None
    n = len(normals[0])
    if any(len(v) != n for v in normals):
        raise ValueError("inconsistent dimensions")
    index = {v:i for i,v in reversed(list(enumerate(normals)))}
    zero = (0,)*n
    if zero in index:
        return {"indices":[index[zero]], "basis":[], "private":[()]}
    for d in range(1, min(rank_cap, n, len(index))+1):
        words = [a for a in product(range(3),repeat=d) if any(a) and a==projectivize(a)]
        full = (1 << len(words)) - 1
        patterns = {a:sum(1 << j for j,b in enumerate(words)
                           if sum(x*y for x,y in zip(a,b))%3 == 0) for a in words}
        for basis in combinations(index,d):
            rows = []
            for a in words:
                v = projectivize(tuple(sum(t*x for t,x in zip(a,col)) for col in zip(*basis)))
                if v == zero:
                    break
                if v in index:
                    rows.append((index[v],patterns[a]))
            else:
                def union(entries):
                    bits = 0
                    for _,m in entries:
                        bits |= m
                    return bits
                if union(rows) != full:
                    continue
                for i in reversed(range(len(rows))):
                    if union(rows[:i]+rows[i+1:]) == full:
                        rows.pop(i)
                private = []
                for i in range(len(rows)):
                    unique = full ^ union(rows[:i]+rows[i+1:])
                    private.append(words[(unique & -unique).bit_length()-1])
                return {"indices":[i for i,_ in rows], "basis":[index[v] for v in basis],
                        "private":private}
    return None

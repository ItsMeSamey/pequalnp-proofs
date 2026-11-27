"""Exact bounded orientable genus for a connected native port permutation."""
from itertools import combinations
import networkx as nx


def cycles(successor):
    seen = set()
    result = []
    for x in range(len(successor)):
        if x in seen:
            continue
        walk = []
        while x not in seen:
            walk.append(x)
            seen.add(x)
            x = successor[x]
        result.append(walk)
    return result


def chart(sigma):
    n = len(sigma)
    if n == 0 or n % 3 or sorted(sigma) != list(range(n)):
        raise ValueError("expected a nonempty native socket permutation")
    nxt = list(range(n,2*n)) + list(sigma)
    chords = []
    for a in range(0,n,3):
        chords.extend([(a,a+1),(n+a,n+a+2)])
    twist = []
    for a,b in chords:
        same = any(a in walk and b in walk for walk in cycles(nxt))
        twist.append(int(not same))
        if not same:
            nxt[a],nxt[b] = nxt[b],nxt[a]
    traces = cycles(nxt)
    if len(traces) != 1:
        raise ValueError("solve connected components separately")
    pos = {v:i for i,v in enumerate(traces[0])}
    intervals = [sorted((pos[a],pos[b])) for a,b in chords]
    matrix = [sum(1<<j for j,(c,d) in enumerate(intervals)
                  if (a<c<b) != (a<d<b)) for a,b in intervals]
    return matrix,twist


def principal_rank(matrix, indices):
    basis = {}
    mask = sum(1<<i for i in indices)
    for i in indices:
        row = matrix[i] & mask
        while row:
            p = row.bit_length()-1
            if p not in basis:
                basis[p] = row
                break
            row ^= basis[p]
    return len(basis)


def assignment(m, clauses):
    implication = nx.DiGraph()
    implication.add_nodes_from(range(2*m))
    for a,b in clauses:
        implication.add_edges_from([(a^1,b),(b^1,a)])
    dag = nx.condensation(implication)
    owner = dag.graph['mapping']
    order = {c:t for t,c in enumerate(nx.topological_sort(dag))}
    if any(owner[2*i]==owner[2*i+1] for i in range(m)):
        return None
    return sum(1<<i for i in range(m) if order[owner[2*i+1]]>order[owner[2*i]])


def bounded_genus(sigma, bound):
    """Return a reversal mask giving genus at most bound, or None."""
    matrix, twist = chart(sigma)
    N = len(matrix)
    nodes = tuple(range(N))
    # Literal 2*g+b denotes the assertion that switch g takes bit b.
    in_x = [2*(i//2)+(1^twist[i]) for i in nodes]

    def side_conditions(base, side):
        # side=0 for X; side=1 for its complement.
        literal = [l^side for l in in_x]
        clauses = [(literal[i],literal[i]) for i in base]
        for a,b in combinations([i for i in nodes if i not in base],2):
            if principal_rank(matrix, (*base,a,b)) > len(base):
                clauses.append((literal[a]^1,literal[b]^1))
        return clauses

    pivots = []
    for d in range(0,min(2*bound,N)+1,2):
        for base in combinations(nodes,d):
            if principal_rank(matrix,base)==d:
                pivots.append(base)
    # Indexing by size avoids iterating over pairs whose total exceeds 2*bound.
    by_size = {}
    for base in pivots:
        by_size.setdefault(len(base),[]).append(base)
    for left in pivots:
        first = side_conditions(left,0)
        for d in range(0,2*bound-len(left)+1,2):
            for right in by_size.get(d,[]):
                if set(left).isdisjoint(right):
                    witness = assignment(N//2,first+side_conditions(right,1))
                    if witness is not None:
                        return witness
    return None


def face_genus(sigma, mask):
    m = len(sigma)//3
    def count(bits):
        step = [sigma[3*(i//3)+(i%3+((bits>>(i//3))&1))%3]
                for i in range(3*m)]
        return len(cycles(step))
    return (2+2*m-count(mask)-count(mask^((1<<m)-1)))//2


if __name__ == '__main__':
    from random import Random
    rng = Random(3153)
    tests = 0
    for m in range(1,6):
        for _ in range(18):
            sigma = rng.sample(range(3*m),3*m)
            try:
                matrix, twist = chart(sigma)
            except ValueError:
                continue
            genera = []
            for mask in range(1<<m):
                left = [i for i in range(2*m) if twist[i]^(mask>>(i//2)&1)]
                right = [i for i in range(2*m) if i not in left]
                g = face_genus(sigma,mask)
                assert 2*g == principal_rank(matrix,left)+principal_rank(matrix,right)
                genera.append(g)
            for bound in range(min(genera)+1):
                got = bounded_genus(sigma,bound)
                assert (got is not None) == (min(genera)<=bound)
                if got is not None:
                    assert genera[got]<=bound
                tests += 1
    print(tests, "genus thresholds matched exhaustive rotation enumeration")

"""Compare raw all-even original-label supports on both sides of the reduction."""
from itertools import combinations, permutations


def make_graph(n, edges):
    rows = [0]*n
    for i,j in edges:
        rows[i] |= 1 << j
        rows[j] |= 1 << i
    return rows


def witnesses(rows, pins):
    free = ((1 << len(rows))-1) ^ pins
    optional = free
    result = set()
    while True:
        w = pins | optional
        if all(not ((row & w).bit_count() % 2) for i,row in enumerate(rows) if w >> i & 1):
            result.add(w)
        if not optional:
            return result
        optional = (optional-1) & free


def compare(rows,z,s,t):
    n = len(rows)
    a = [i for i in range(n) if i not in (t,z)]
    local = {v:i for i,v in enumerate(a)}
    p,q,b,d,e,root = range(len(a),len(a)+6)
    edges = [(i,j) for i,j in combinations(range(len(a)),2) if rows[a[i]] >> a[j] & 1]
    edges += [(p,i) for i in range(len(a))] + [(b,i) for i in range(len(a))]
    edges += [(q,b),(b,e),(d,local[s])]
    edges += [(e,i) for i,v in enumerate(a) if bool(rows[t] >> v & 1) != (v == s)]
    edges += [(root,i) for i in range(root)]
    reduced = make_graph(root+1,edges)
    orig = witnesses(rows,(1 << z) | (1 << s) | (1 << t))
    raw = witnesses(reduced,(1 << root) | (1 << p) | (1 << q))
    forced = sum(1 << v for v in (p,q,b,d,e,root))
    forward = {forced | sum(1 << i for i,v in enumerate(a) if w >> v & 1) for w in orig}
    backward = {(1 << z) | (1 << t) | sum(1 << v for i,v in enumerate(a) if w >> i & 1)
                for w in raw}
    assert forward == raw and backward == orig and len(raw) == len(orig)
    return len(raw)


if __name__ == '__main__':
    cases = yes = total = 0
    for n in range(3,6):
        pairs = list(combinations(range(n),2))
        for pattern in range(1 << len(pairs)):
            rows = make_graph(n,[edge for i,edge in enumerate(pairs) if pattern >> i & 1])
            for z,s,t in permutations(range(n),3):
                if rows[z].bit_count() == n-1:
                    count = compare(rows,z,s,t)
                    cases += 1
                    yes += bool(count)
                    total += count
    print(cases, 'ordered rooted instances;', yes, 'YES;', total, 'witnesses')

"""Small independent row-trie, padding and patch replay for native transition schemas."""
from itertools import product


def index_clause(index):
    row, kind, slot = index & 7, index >> 3 & 7, index >> 6 & 3
    # Higher index bits are unused; never copied into a variable name.
    def name(tag, r, minor):
        return (tag << 7) | (r << 4) | (minor << 2)
    local, sort, fetch, config = [name(t, row, 0) for t in range(4)]
    left = (row * 2) % 8 + (row >> 2)
    right = (row >> 1) + (row % 2) * 4
    dummy = name(4, 0, 0)
    if kind == 0:
        a, b = name(1, left, 1), name(1, left ^ 1, 2)
        return (((a,0),(b,0),(sort,1)), ((sort,0),(a,1),(a,1)),
                ((sort,0),(b,1),(b,1)), ((dummy,1),(dummy,0),(dummy,1)))[slot]
    if kind < 6:
        parent, child = ((local, config), (local, sort), (sort, config),
                         (fetch, name(2,(row,left,right,row & 6)[slot],1)),
                         (local,name(2,slot,2)))[kind-1]
        s = slot & 1
        return ((parent,s),(child,1-s),(child,1-s))
    return ((dummy,1),)*3 if kind == 6 else ((dummy,1),(dummy,0),(dummy,1))


def key(addr):
    return addr >> 7, format(addr >> 4 & 7, '03b')


def leaves(addr, split):
    tag, row = key(addr)
    return tag, next(row[:i] for i in range(4) if (tag,row[:i]) not in split)


def traverse(rows, split):
    # Literal feasibility on the original clause address domain, not a list of leaf triples.
    frontier = {tuple((tag,'') for tag in tags) for tags in product(range(5), repeat=3)}
    done = set()
    while frontier:
        following = set()
        for node in frontier:
            if not any(all(t == at and ar.startswith(p) for (t,p),(at,ar) in zip(node,r))
                       for r in rows):
                continue
            if all(x not in split for x in node):
                done.add(node)
                continue
            choices = [[(t,p+'0'),(t,p+'1')] if (t,p) in split else [(t,p)] for t,p in node]
            following.update(product(*choices))
        frontier = following
    return done


def main():
    clauses = [index_clause(i) for i in range(256)]
    assert all(index_clause(i | 256) == c for i,c in enumerate(clauses))
    rows = [tuple(key(a) for a,_ in c) for c in clauses]
    occurring = {a for c in clauses for a,_ in c}
    assert all(a % 4 == 0 for a in occurring)
    truth = {a:1 for a in occurring}
    assert all(any(truth[a] == s for a,s in c) for c in clauses)
    errors = {a for a in occurring if key(a) in {(1,'111'),(2,'001'),(4,'000')}}
    damaged = {a: b ^ (a in errors) for a,b in truth.items()}
    assert any(all(damaged[a] != s for a,s in c) for c in clauses)
    paths = {(t,r[:i]) for a in errors for t,r in [key(a)] if t != 4 for i in range(3)}
    patch = {}
    for a in errors:
        leaf = leaves(a, paths)
        assert leaf[0] == 4 or len(leaf[1]) == 3
        patch.setdefault(leaf,{})[a] = truth[a]
    for c in clauses:
        for a,s in c:
            value = patch.get(leaves(a,paths),{}).get(a,damaged[a])
            assert (value == s) == (truth[a] == s)
    shapes = [set(),paths,{(0,''),(0,'0'),(0,'01'),(3,''),(3,'1'),(2,'')},
              {(t,p) for t in range(4) for p in ('','0','1','10','11')}]
    for split in shapes:
        assert traverse(rows,split) == {tuple(leaves(a,split) for a,_ in c) for c in clauses}
    # Unary segments may end in padding zeros. Interior holes need separate strata.
    for mask in (7,6,4,0):
        image = [r & mask for r in range(8)]
        assert image == sorted(image)
    assert (3 & 5) > (4 & 5) or (1 & 5) > (2 & 5)
    print('Irregular shapes, raw clauses, canonical padding and full-row literal repairs passed.')


if __name__ == '__main__':
    main()

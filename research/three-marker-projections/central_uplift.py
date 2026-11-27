"""Certified reduction on a supplied indexed central-port decomposition."""
from collections import deque
from itertools import combinations
from component_nullity import dependencies, bits

def combine(values, mask):
    result = 0
    for i in bits(mask):
        result ^= values[i]
    return result

def mul(x, y, k):
    if k == 1:
        return x, y
    if k == 2:
        return y, x ^ y
    return x ^ y, x

def rank(cols):
    piv = {}
    for x,y in cols:
        while x | y:
            i = (x|y).bit_length()-1
            k = ((x>>i)&1) + 2*((y>>i)&1)
            if i not in piv:
                piv[i] = mul(x,y,(0,1,3,2)[k])
                break
            a,b = mul(*piv[i], k)
            x ^= a
            y ^= b
    return len(piv)

def three_connected(cols):
    """Pinned 2-separation via the matroid intersection min-max formula."""
    full = rank(cols)
    n = len(cols)
    if n < 4:
        return False
    for s in combinations(range(n),2):
        rest = set(range(n)) - set(s)
        for t in combinations(sorted(rest),2):
            if s > t:
                continue
            def good(seed, ids):
                rows = [cols[i] for i in (*seed,*ids)]
                return rank(rows) == len(rows)
            if not good(s,[]) or not good(t,[]):
                return False
            chosen = set()
            ground = rest - set(t)
            while len(chosen)+4-full < 2:
                outside = ground-chosen
                pred = {i:None for i in outside if good(s,chosen|{i})}
                q = deque(pred)
                end = None
                while q and end is None:
                    i = q.popleft()
                    if i in chosen:
                        adj = [j for j in outside if good(s,(chosen-{i})|{j})]
                    else:
                        if good(t,chosen|{i}):
                            end = i
                            break
                        adj = [j for j in chosen if good(t,(chosen-{j})|{i})]
                    for j in adj:
                        if j not in pred:
                            pred[j] = i
                            q.append(j)
                if end is None:
                    return False
                while end is not None:
                    chosen.symmetric_difference_update([end])
                    end = pred[end]
    return True

def reduce_central(private,height,tag,tree,three_name=None):
    if three_name is None:
        from three_name_adapter import three_name
    n = len(private)
    if len(height)!=n or len(tag)!=n or any(x<0 for x in private):
        raise ValueError("invalid physical columns")
    if any(x not in range(4) for x in [*height,*tag]):
        raise ValueError("invalid named bits")
    # Fundamental circuits generate each private component.
    components = [{i} for i in range(n)]
    for relation in dependencies(private):
        merged = set(bits(relation))
        separate = []
        for component in components:
            if merged & component:
                merged.update(component)
            else:
                separate.append(component)
        components = separate + [merged]
    if len(components) != 1:
        raise ValueError("private matroid must be connected")
    top = 1 << max((x.bit_length() for x in private),default=0)
    special = (top,0)
    def lift(p,h):
        return p | (top if h&1 else 0), top if h&2 else 0
    lifted = [lift(p,h) for p,h in zip(private,height)]
    full = rank(lifted+[special])
    def collect(node):
        if type(node) is int:
            if node not in range(n):
                raise ValueError("invalid physical index")
            return [node]
        if not isinstance(node,(list,tuple)) or len(node)<2:
            raise ValueError("invalid tree node")
        ids = [i for child in node for i in collect(child)]
        outside = [lifted[i] for i in sorted(set(range(n))-set(ids))]+[special]
        if len(outside)<2 or rank([lifted[i] for i in ids])+rank(outside)-full!=1:
            raise ValueError("improper 2-separation")
        return ids
    branches = [collect(node) for node in tree]
    if sorted(i for group in branches for i in group)!=list(range(n)):
        raise ValueError("tree must partition physical IDs")
    ports = []
    for group in branches:
        ps = [private[i] for i in group]
        hs = [height[i] for i in group]
        if any(combine(hs,r) for r in dependencies(ps)):
            raise ValueError("branch spans distinguished point")
        outside = [private[i] for i in sorted(set(range(n))-set(group))]
        mask = (1<<len(group))-1
        images = set()
        for r in dependencies(ps+outside):
            b = combine(ps,r&mask)
            if b:
                images.add((b,combine(hs,r&mask)))
        if len(images)!=1:
            raise ValueError("private interface must be a line")
        ports.append(images.pop())
    if not three_connected([special]+[lift(p,h) for p,h in ports]):
        raise ValueError("central torso is not 3-connected")
    if len({combine(height,r) for r in dependencies(private)}-{0})<2:
        raise ValueError("height rank below two")
    columns, expressions = [], []
    for group,(b,h) in zip(branches,ports):
        ps = [private[i] for i in group]
        ts = [tag[i] for i in group]
        virtual = len(group)
        for u in range(4):
            selected = three_name(ps+[b],ts+[4],4|u)
            if selected is None:
                continue
            selected = list(selected)
            if len(set(selected))!=len(selected) or virtual not in selected or any(i not in range(virtual+1) for i in selected):
                raise ValueError("invalid three-name witness IDs")
            local = [i for i in selected if i!=virtual]+[virtual]
            names = [(ts+[4])[i] for i in local]
            rels = dependencies([(ps+[b])[i] for i in local])
            gains = {combine(names,r) for r in rels}
            if (4|u) not in gains or not gains<={0,4|u}:
                raise ValueError("incorrect three-name trace")
            rel = next(r for r in rels if r>>(len(local)-1))
            ids = [group[i] for j,i in enumerate(local[:-1]) if (rel>>j)&1]
            columns.append((b,h,u))
            expressions.append(ids)
    return columns,expressions


def expand_witness(columns, expressions, selected, private, height, tag):
    """Verify indexed expansion without accepting negative or duplicate IDs."""
    def validate(ids, length):
        ids = list(ids)
        if any(type(i) is not int or i not in range(length) for i in ids):
            raise ValueError("invalid witness index")
        if len(set(ids)) != len(ids):
            raise ValueError("duplicate witness index")
        return ids
    n = len(private)
    if len(columns) != len(expressions) or len(height) != n or len(tag) != n:
        raise ValueError("inconsistent expansion tables")
    selected = validate(selected, len(columns))
    expressions = [validate(ids,n) for ids in expressions]
    def exact(ps,hs,ts):
        gains = {combine(hs,r)|(combine(ts,r)<<2) for r in dependencies(ps)}
        return all(v<4 for v in gains) and len(gains-{0})>=2
    selected = list(selected)
    if not exact(*([columns[i][j] for i in selected] for j in range(3))):
        raise ValueError("invalid central trace")
    ids = sorted({i for j in selected for i in expressions[j]})
    if not exact(*([v[i] for i in ids] for v in (private,height,tag))):
        raise ValueError("incorrect expanded trace")
    return ids

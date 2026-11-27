"""Original NAND model counts by affine tap-factor separators."""
from dataclasses import dataclass
from affine_independence_portfolio import basis
from pivot_cone_rewrite import _xor
from primitive_rewrite_chain import _inputs, evaluate
from quadratic_polar_online import _space


def _coordinates(word, rows):
    result = 0
    for i,row in enumerate(rows):
        if word & (1 << (row.bit_length()-1)):
            word ^= row
            result |= 1 << i
    if word:
        raise AssertionError('form outside separator span')
    return result


def _intersection(left,right):
    pivots = {u.bit_length()-1:(u,0) for u in left}
    common = []
    for original in right:
        v = tag = original
        while v:
            j = v.bit_length()-1
            if j not in pivots:
                pivots[j] = v,tag
                break
            a,b = pivots[j]
            v,tag = v^a,tag^b
        if not v and tag:
            common.append(tag)
    return basis(common)


def _project(word, masks):
    return sum(((word & m).bit_count() % 2) << i for i,m in enumerate(masks))


def _extract(n, gates, out):
    form = {-1:0,-2:1}
    form.update((i,1 << (n-i)) for i in range(n))
    gates_by_bit = {}
    for w,(a,b) in enumerate(gates,n):
        x,y = form[a],form[b]
        pair = _xor(n,gates,a,b)
        if pair is not None:
            form[w] = form[pair[0]] ^ form[pair[1]]
        elif x == 0 or y == 0 or x == (y ^ 1):
            form[w] = 1
        elif x == 1:
            form[w] = y ^ 1
        elif y == 1 or x == y:
            form[w] = x ^ 1
        else:
            pos = n+len(gates_by_bit)
            form[w] = 1 << (pos+1)
            gates_by_bit[pos] = (x,y,form[w])
    required = form[out] >> 1
    live = []
    for pos,terms in reversed(gates_by_bit.items()):
        if required & (1 << pos):
            required |= (terms[0] | terms[1]) >> 1
            live.append(terms)
    live.reverse()
    live.append((form[out],))
    return live,n+len(live)-1,n+len(gates_by_bit)


@dataclass
class _Node:
    scope: tuple
    children: tuple = ()
    boundary: tuple = ()
    enumerated: tuple = ()
    counts: dict | None = None
    choices: dict | None = None


def solve(n, F, *, merges=None, max_states=None):
    """Exact count/witness or UNKNOWN when the requested table cap is too small.

    Leaves are source-ordered residual NAND factors followed by the output pin.
    Optional merges name pairs of active leaves or earlier merge nodes. The
    default tree merges consecutive groups in balanced rounds.
    """
    gates,out = F
    gates = _inputs(n,gates,out)
    if max_states is not None and (type(max_states) is not int or max_states < 0):
        raise ValueError('invalid state budget')
    factors,ambient,physical = _extract(n,gates,out)
    nodes = [_Node(basis(x >> 1 for x in terms)) for terms in factors]
    count = len(nodes)
    def join(a,b):
        nodes.append(_Node(basis((*nodes[a].scope,*nodes[b].scope)),(a,b)))
        return len(nodes)-1
    if merges is None:
        active = list(range(count))
        while len(active)>1:
            following = [join(active[i],active[i+1]) for i in range(0,len(active)-1,2)]
            if len(active)%2:
                following.append(active[-1])
            active = following
    else:
        active = set(range(count))
        for a,b in merges:
            if type(a) is not int or type(b) is not int or a==b or a not in active or b not in active:
                raise ValueError('invalid merge schedule')
            active.remove(a)
            active.remove(b)
            active.add(join(a,b))
        if len(active)!=1:
            raise ValueError('incomplete merge schedule')

    stack = [(len(nodes)-1,())]
    while stack:
        i,outside = stack.pop()
        node = nodes[i]
        node.boundary = _intersection(node.scope,outside)
        if node.children:
            a,b = node.children
            stack.append((a,basis((*outside,*nodes[b].scope))))
            stack.append((b,basis((*outside,*nodes[a].scope))))
    for node in nodes:
        if node.children:
            a,b = node.children
            node.enumerated = basis((*nodes[a].boundary,*nodes[b].boundary))
        else:
            node.enumerated = node.scope
    width = max(len(node.enumerated) for node in nodes)
    required = 1 << width
    if max_states is not None and required > max_states:
        return dict(status='unknown',reason='separator_budget',required=required,available=max_states)

    for i,node in enumerate(nodes):
        rows = node.enumerated
        project = tuple(_coordinates(v,rows) for v in node.boundary)
        if node.children:
            a,b = node.children
            left = tuple(_coordinates(v,rows) for v in nodes[a].boundary)
            right = tuple(_coordinates(v,rows) for v in nodes[b].boundary)
        else:
            local = tuple(_coordinates(x >> 1,rows) for x in factors[i])
            offset = sum((x & 1) << j for j,x in enumerate(factors[i]))
        node.counts,node.choices = {},{}
        for assignment in range(1 << len(rows)):
            key = _project(assignment,project)
            if node.children:
                ka,kb = _project(assignment,left),_project(assignment,right)
                total = nodes[a].counts.get(ka,0)*nodes[b].counts.get(kb,0)
                choice = ka,kb
            else:
                pattern = _project(assignment,local)^offset
                total = int(pattern == 1 if len(local)==1 else
                            (pattern >> 2) == (1 ^ int((pattern & 3)==3)))
                choice = assignment
            if total:
                node.counts[key] = node.counts.get(key,0)+total
                node.choices.setdefault(key,choice)
    raw_count = nodes[-1].counts.get(0,0) << (ambient-len(nodes[-1].scope))
    witness = None
    if raw_count:
        equations = []
        stack = [(len(nodes)-1,0)]
        while stack:
            i,key = stack.pop()
            node = nodes[i]
            choice = node.choices[key]
            if node.children:
                stack.extend(zip(node.children,choice))
            else:
                equations.extend((r,(choice>>j)&1) for j,r in enumerate(node.scope))
        all_bits = _space(physical,equations)[0]
        witness = all_bits & ((1 << n)-1)
        if not evaluate(n,gates,out,witness):
            raise AssertionError('separator witness failed original NAND check')
    return dict(status='witness' if raw_count else 'unsat',count=raw_count,
                assignment=witness,separator_width=width,factors=count,
                global_rank=len(nodes[-1].scope))


def padded_path_source(n,padding=0):
    """Dense tap path on n=6k active coordinates and optional shared padding."""
    if type(n) is not int or n < 6 or n%6 or type(padding) is not int or padding<0:
        raise ValueError('positive multiple of six and nonnegative padding required')
    h = n+padding
    gates = []
    def nand(a,b):
        gates.append((a,b))
        return h+len(gates)-1
    def xor(a,b):
        middle = nand(a,b)
        return nand(nand(a,middle),nand(b,middle))
    total = 0
    for i in range(1,h):
        total = xor(total,i)
    taps = [xor(total,i) for i in range(n)]
    out = -2
    for a,b in zip(taps,taps[1:]):
        clause = nand(a,b)
        joined = nand(out,clause)
        out = nand(joined,joined)
    return h,(tuple(gates),out)

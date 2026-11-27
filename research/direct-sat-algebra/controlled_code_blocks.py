"""Positive separator DP for an aligned control pencil, with exact terminal characters.

Tree format: a control index, or a tuple (left, right). solve returns a count
(or Boolean for decision_only), an optional (x,y) witness and planning statistics.
The packed input conventions are those of controlled_witness_radius.
"""
from dataclasses import dataclass
from controlled_witness_radius import ProjectedOracle, column_basis, row_equations
from quadratic_target import affine_domain, apply_basis, insert, parity, reduce_vector


def balanced(items):
    items = list(items)
    if not items:
        return None
    if len(items) == 1:
        return items[0]
    middle = len(items)//2
    return balanced(items[:middle]), balanced(items[middle:])


def interface(cols, others, target, width):
    """Compute affine intersection in independent coordinates, without enumerating it."""
    local = [v for v, _ in column_basis(cols).values()]
    outside = column_basis(others)
    residues = [reduce_vector(v, outside)[0] for v in local]
    right = reduce_vector(target, outside)[0]
    flat = affine_domain(len(local), row_equations(residues, right, width))
    if flat is None:
        return None
    offset, dirs, _ = flat
    return apply_basis(local, offset), [apply_basis(local, d) for d in dirs]


@dataclass
class Node:
    sites: tuple
    flat: tuple
    basis: dict
    cost: int
    action: str
    children: tuple
    counts: dict
    choices: dict

    @property
    def width(self):
        return len(self.flat[1])


def solve(m, A, b, U, activators, tree=None, *, decision_only=False, policy="auto"):
    if policy not in ("auto", "split", "terminal"):
        raise ValueError("policy must be auto, split or terminal")
    A, U, activators = tuple(A), tuple(U), tuple(activators)
    n, k = len(A), len(U)
    if m < 0 or len(activators) != k or any(not 0<=v<1<<m for v in (*A,b,*U)):
        raise ValueError("invalid output dimension or columns")
    if any(not 0<=v<1<<n or c not in (0,1) for v,c in activators):
        raise ValueError("invalid activators")
    tree = balanced(range(k)) if tree is None else tree

    def unpack(t):
        if isinstance(t,int):
            return (t,)
        if not isinstance(t,tuple) or len(t)!=2:
            raise ValueError("invalid tree node")
        return unpack(t[0])+unpack(t[1])
    if (tree is not None and sorted(unpack(tree))!=list(range(k))) or (tree is None and k):
        raise ValueError("tree must contain every control exactly once")

    width = k+m
    data = [sum(((v>>j)&1)<<i for i,(v,_) in enumerate(activators)) | (A[j]<<k)
            for j in range(n)]
    kernel = column_basis(data)
    lift_size = n-len(kernel)
    shift = sum(c<<i for i,(_,c) in enumerate(activators)) | (b<<k)

    def quotient(v):
        return reduce_vector(v,kernel)[0]
    h = quotient(shift)
    qa = [quotient(1<<i) for i in range(k)]
    wd = [quotient(u<<k) for u in U]
    stats = {"lift_dimension":lift_size, "max_width":0, "joins":0, "terminals":0,
             "max_terminal_rank":0, "max_active_width":0, "clock":0}
    if reduce_vector(h,column_basis(qa+wd))[0]:
        return (False if decision_only else 0), None, stats

    def plan(t):
        children = () if isinstance(t,int) else tuple(plan(c) for c in t)
        sites = (t,) if not children else children[0].sites+children[1].sites
        members=set(sites)
        local=[v for i in sites for v in (qa[i],wd[i])]
        others=[v for i in range(k) if i not in members for v in (qa[i],wd[i])]
        flat=interface(local,others,h,width)
        if flat is None:
            raise AssertionError("globally consistent code has empty interface")
        w=len(flat[1])
        stats["max_width"]=max(stats["max_width"],w)
        offset, directions=flat
        membership=column_basis(directions)
        if not children:
            return Node(sites,(offset,directions),membership,4,"leaf",(),{}, {})
        D=len(column_basis(wd[i] for i in sites))
        terminal_cost=1<<(w+D)
        split_cost=sum(c.cost for c in children)+(1<<sum(c.width for c in children))
        use_terminal=policy=="terminal" or (policy=="auto" and terminal_cost<split_cost)
        return Node(sites,flat,membership,terminal_cost if use_terminal else split_cost,
                    "terminal" if use_terminal else "join",children,{}, {})

    def oracle(node,g):
        sites=node.sites
        return ProjectedOracle(width,[qa[i] for i in sites],g,[wd[i] for i in sites],
                               [(1<<j,0) for j in range(len(sites))],{},())

    def record(node,g,value,choice):
        if value and not reduce_vector(g^node.flat[0],node.basis)[0]:
            node.counts[g]=True if decision_only else node.counts.get(g,0)+value
            node.choices.setdefault(g,choice)

    def run(node):
        stats["max_active_width"]=max(stats["max_active_width"],node.width)
        if node.action=="leaf":
            i=node.sites[0]
            for q,w,weight in ((0,0,2),(1,0,1),(1,1,1)):
                record(node,(qa[i] if q else 0)^(wd[i] if w else 0),weight,(q,w))
        elif node.action=="terminal":
            stats["terminals"]+=1
            D=len(column_basis(wd[i] for i in node.sites))
            stats["max_terminal_rank"]=max(stats["max_terminal_rank"],D)
            off,dirs=node.flat
            for mask in range(1<<len(dirs)):
                g=off^apply_basis(dirs,mask)
                record(node,g,oracle(node,g).count(),None)
        else:
            stats["joins"]+=1
            left,right=node.children
            run(left)
            run(right)
            for a,v in left.counts.items():
                for d,w in right.counts.items():
                    record(node,a^d,v*w,(a,d))

    def lift(node,g):
        if node.action=="leaf":
            q,w=node.choices[g]
            i=node.sites[0]
            return q<<i,w<<i
        if node.action=="join":
            gl,gr=node.choices[g]
            ql,wl=lift(node.children[0],gl)
            qr,wr=lift(node.children[1],gr)
            return ql|qr,wl|wr
        q=oracle(node,g).witness_y()
        if q is None:
            raise AssertionError("terminal backpointer infeasible")
        rows={}
        for j,i in enumerate(node.sites):
            if q>>j&1:
                insert(wd[i],1<<i,rows)
        target=g^apply_basis([qa[i] for i in node.sites],q)
        resid,w=reduce_vector(target,rows)
        if resid:
            raise AssertionError("terminal controls did not lift")
        return sum(((q>>j)&1)<<i for j,i in enumerate(node.sites)),w

    if tree is None:
        q=w=0
        count=1
    else:
        root=plan(tree)
        stats["clock"]=root.cost
        run(root)
        count=root.counts.get(h,0)
        if not count:
            return (False if decision_only else 0),None,stats
        q,w=lift(root,h)
    target=(q | (apply_basis(U,w)<<k)) ^ shift
    data_lift=affine_domain(n,row_equations(data,target,width))
    if data_lift is None:
        raise AssertionError("global codeword did not lift")
    return (True if decision_only else count<<lift_size),(w,data_lift[0]),stats

"""Constructive two-readout solver for mixed physical thirteen-state tables."""
from itertools import combinations, product

from arbitrary_fourteen_solver import Network, component, parity
from general_fourteen_check import bits, fixed, verify


def classify(table):
    """Recognize the theorem's three active-endpoint relations exactly."""
    if not 0 <= table <= 65535 or table.bit_count() < 13:
        raise ValueError("expected at least thirteen raw states")
    fibers = tuple({d&s for d in range(4) if table >> (4*s+d) & 1} for s in range(4))
    if fibers[1] == {0,1} and fibers[2] == {0,2}:
        if len(fibers[3]) == 1:
            return "double", next(iter(fibers[3]))
        if all({d & bit for d in fibers[3]} == {0,bit} for bit in (1,2)):
            return "ordinary", None
    for tail,release,forced in product(range(2),repeat=3):
        expected = tuple({d&s for d in range(4) if not s >> tail & 1
                          or (s >> (1-tail) & 1) == release or (d >> tail & 1) == forced}
                         for s in range(4))
        if expected == fibers:
            return "directed", (tail,release,forced)
    raise ValueError("unsupported active-endpoint relation")


class Model:
    def __init__(self, rows, c, edges, slack):
        self.n = len(rows)
        self.full = (1 << self.n)-1
        self.rows = [row & ~(1 << i) for i,row in enumerate(rows)]
        self.offset = c ^ sum(row & (1 << i) for i,row in enumerate(rows))
        self.slack = slack
        self.ordinary, self.double, self.directed = [], [], []
        for i,j,table in edges:
            kind,data = classify(table)
            if kind == "ordinary":
                self.ordinary.append((i,j,table))
            elif kind == "double":
                self.double.append((i,j))
                self.offset ^= ((data&1)<<i) | ((data>>1)<<j)
            else:
                end,release,forced = data
                tail,head = (i,j) if end == 0 else (j,i)
                self.directed.append((tail,head,release))
                self.offset ^= forced << tail


class View(Network):
    """Current induced graph in original coordinates; base holds removed ones."""
    def __init__(self, model, live, base, extra_slack=0):
        self.model, self.live, self.base = model, live, base
        self.n, self.full = model.n, model.full
        self.rows, self.offset = model.rows, model.offset
        self.releases = [[] for _ in self.rows]
        self.ord_adj = [0]*self.n
        self.adj = [0]*self.n
        slack = model.slack | extra_slack
        for tail,head,release in model.directed:
            slack |= 1 << head
            if live >> head & 1:
                self.releases[tail].append((head,release))
            elif (base >> head & 1) == release:
                slack |= 1 << tail
        for ordinary,edges in ((True,model.ordinary),(False,model.double)):
            for edge in edges:
                i,j = edge[:2]
                for v,w in ((i,j),(j,i)):
                    if not live >> v & 1:
                        continue
                    if live >> w & 1:
                        self.adj[v] |= 1 << w
                        if ordinary:
                            self.ord_adj[v] |= 1 << w
                    elif not base >> w & 1:
                        slack |= 1 << v
                    elif ordinary:
                        raise AssertionError("selected removed ordinary neighbor")
        self.U = 0
        for i in bits(slack & live):
            if not self.U >> i & 1:
                self.U |= component(i,self.ord_adj)
        self.S = live ^ self.U
        for i,j in model.double:
            for v,w in ((i,j),(j,i)):
                if self.S >> v & 1 and self.U >> w & 1:
                    self.releases[v].append((w,0))
        self.adj = [row & self.S for row in self.adj]
        self.singletons = sum(1 << i for i in bits(self.S) if not self.adj[i])

    def one(self, equations):
        return self.single_rank(self.S,self.U,self.base,equations)

    def free_pair(self, i, j):
        for left,right in product([None,*self.releases[i]],[None,*self.releases[j]]):
            if left and right and left[0] == right[0] and left[1] != right[1]:
                continue
            a = bool(self.adj[i] & ~(1<<j)) or left is not None
            b = bool(self.adj[j] & ~(1<<i)) or right is not None
            if not ((a and b) or ((a or b) and (self.ord_adj[i] >> j & 1))):
                continue
            word = sum(1<<h for h,val in {s for s in (left,right) if s} if val)
            target = self.target
            for v in bits(word):
                target ^= self.labels[v]
            for x,y in product(range(2),repeat=2):
                if x*self.labels[i] ^ y*self.labels[j] == target:
                    return self.base | word | (x<<i) | (y<<j)
        return None

    def demand(self, i, value=0):
        return self.rows[i], (self.offset >> i & 1) ^ value

    def two_fixed(self, i, j, satellites=0, try_release=True):
        removed = satellites | (1<<i) | (1<<j)
        child = View(self.model,self.live ^ removed,self.base | removed)
        # Double baselines were absorbed globally. Only ordinary edges can
        # change the internal pair's 11 defect relative to those baselines.
        totals = {0}
        for p,q,table in self.model.ordinary:
            if {p,q} == {i,j}:
                opts = [d if p == i else ((d&1)<<1 | d>>1)
                        for d in range(4) if table >> (12+d) & 1]
                totals = {k^d for k in totals for d in opts}
        if try_release:
            for v,w,shift in ((i,j,1),(j,i,0)):
                projection = {k >> shift & 1 for k in totals}
                for head,release in self.releases[v]:
                    pin = [(1<<head,release)]
                    if len(projection) == 2:
                        word = child.one(pin)
                        if word is not None:
                            return word
                    else:
                        baseline = next(iter(projection))
                        for other in [None,*self.releases[w]]:
                            eqs = pin + [self.demand(w,baseline ^ int(other is not None))]
                            if other:
                                eqs.append((1<<other[0],other[1]))
                            word = child.one(eqs)
                            if word is not None:
                                return word
        if len(totals) == 1:
            k = next(iter(totals))
            return child,[self.demand(i,k&1),self.demand(j,k>>1)]
        for first,second in combinations(sorted(totals),2):
            delta = first ^ second
            normal = (delta>>1) | ((delta&1)<<1)
            row,rhs = 0,parity(normal & first)
            for axis,v in ((1,i),(2,j)):
                if normal & axis:
                    a,b = self.demand(v)
                    row ^= a
                    rhs ^= b
            word = child.one([(row,rhs)])
            if word is not None:
                return word
        return None

    def star(self, h, marked):
        satellites = sum(1<<v for v in bits(self.S) if self.adj[v] == 1<<h
                         and not self.releases[v] and not self.ord_adj[v])
        assert not marked & ~satellites
        center = component(h,self.ord_adj)
        base_eq = [(1<<h,1),(marked,1)]
        probes = {(v,0) for v in bits((center|satellites) ^ (1<<h))}
        for v in bits(center):
            probes.update(self.releases[v])
            for i,j in self.model.double:
                if v in (i,j):
                    other = j if v == i else i
                    if self.live >> other & 1 and not center >> other & 1:
                        probes.add((other,0))
        relaxed = View(self.model,self.live,self.base,1<<h)
        for v,value in probes:
            if relaxed.U >> v & 1:
                word = relaxed.one(base_eq + [(1<<v,value)])
            else:
                assert value == 0
                trial = View(self.model,self.live ^ (1<<v),self.base,1<<h)
                word = trial.one(base_eq)
            if word is not None:
                return word
        if not parity(marked & satellites):
            return None
        pinned = satellites | (1<<h)
        base = self.base | pinned
        remain = self.live ^ pinned
        constraints = set()
        for v in bits(satellites):
            row,rhs = self.demand(v)
            row,rhs = row & remain,rhs ^ parity(row & base)
            if not row and rhs:
                return None
            if row:
                constraints.add((row,rhs))
        if any((row,rhs^1) in constraints for row,rhs in constraints):
            return None
        if len(constraints) > 1:
            if self.y_space(list(constraints),remain) is None:
                return None
            raise AssertionError("nonempty forced satellite slice has codimension >1")
        if center == 1<<h:
            child = View(self.model,remain,base)
            return child,list(constraints)+[self.demand(h)]
        assert center.bit_count() == 2
        k = next(bits(center ^ (1<<h)))
        assert constraints == {(1<<k,1)}
        return self.two_fixed(h,k,satellites,try_release=False)

    def stage(self, equations):
        self.labels = [sum(((row >> i)&1)<<j for j,(row,_) in enumerate(equations))
                       for i in range(self.n)]
        self.target = sum((rhs ^ parity(row & self.base))<<j
                          for j,(row,rhs) in enumerate(equations))
        marked = [v for v in bits(self.S) if self.labels[v]]
        if len({self.labels[v] for v in marked}) <= 1:
            return self.one(equations)
        pairs = [(i,j) for i,j in combinations(marked,2) if self.labels[i] != self.labels[j]]
        for i,j in pairs:
            word = self.free_pair(i,j)
            if word is not None:
                return word
        i,j = pairs[0]
        if self.singletons >> i & 1:
            assert self.singletons >> j & 1
            head = self.releases[i][0][0]
            for value in (0,1):
                released = sum(1<<v for v in marked if (head,value) in self.releases[v])
                word = self.single_rank(self.S ^ released,self.U | released,self.base,
                                        equations + [(1<<head,value)])
                if word is not None:
                    return word
            return None
        for toss in [0,*(1<<v for v in marked)]:
            word = self.single_rank(0,self.U,self.base | toss,equations)
            if word is not None:
                return word
        colors = {self.labels[v] for v in marked}
        assert len(colors) == 2 and not any(self.labels[v] for v in bits(self.U))
        if self.adj[i] == 1<<j and self.adj[j] == 1<<i:
            return self.two_fixed(i,j)
        left,right = ([v for v in marked if self.labels[v] == k] for k in colors)
        if len(right) == 1 and (len(left)>1 or self.adj[right[0]].bit_count()>1):
            left,right = right,left
        assert len(left) == 1
        return self.star(left[0],sum(1<<v for v in right))


def solve(rows, c, edges, labels, target, permanent=0):
    """Return (original occupancy, raw edge defects), or None for infeasibility.

    Each edge is (i,j,table), using bit 4*occupancy+defects in endpoint
    low-bit-first order. At an optional permanent-slack site, the missing
    correction is the residual XOR of its returned defects and native drift.
    """
    n = len(rows)
    full = (1 << n)-1
    if len(labels) != n or any(not 0 <= v < 4 for v in labels) or not 0 <= target < 4:
        raise ValueError("expected two-bit readout columns and target")
    if c & ~full or permanent & ~full or any(row & ~full for row in rows):
        raise ValueError("bit outside site range")
    if any(not rows[j] >> i & 1 for i,row in enumerate(rows) for j in bits(row)):
        raise ValueError("drift matrix must be symmetric off the diagonal")
    edges = list(edges)
    covered = permanent
    for i,j,_ in edges:
        if not (0 <= i < n and 0 <= j < n and i != j):
            raise ValueError("invalid edge endpoints")
        covered |= (1<<i) | (1<<j)
    if covered != full:
        raise ValueError("every original site needs an incidence or slack")
    model = Model(rows,c,edges,permanent)
    view = View(model,full,0)
    equations = [(sum(((label>>b)&1)<<i for i,label in enumerate(labels)), target>>b&1)
                 for b in (0,1)]
    while True:
        result = view.stage(equations)
        if not isinstance(result,tuple):
            break
        view,equations = result
    if result is None:
        return None
    observed = 0
    for i in bits(result):
        observed ^= labels[i]
    assert observed == target
    # A full table to a vacant dummy supplies an independent physical slack
    # at each requested site during final original-coordinate reconstruction.
    check_rows = list(rows) + ([0] if permanent else [])
    check_edges = edges + [(i,n,65535) for i in bits(permanent)]
    defects = fixed(check_rows,c,check_edges,result)
    assert defects is not None and verify(check_rows,c,check_edges,result,defects)
    return result,defects[:len(edges)]

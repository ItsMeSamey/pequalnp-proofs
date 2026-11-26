"""Graphic trace tables on a supplied neighborhood partition, with arbitrary demands."""
from itertools import combinations, product
from macro import canonical, eliminate, functional, image, intersection, solve


class GraphicBlock:
    def __init__(self, columns, edges, nvertices, classes):
        self.cols = tuple(columns)
        self.edges = tuple(edges)
        self.n = nvertices
        self.parts = tuple(tuple(p) for p in classes)
        if len(self.cols) != len(self.edges) or sorted(v for p in self.parts for v in p) != list(range(self.n)):
            raise ValueError("graph certificate must list all ordinary edges and vertices")
        if any(not p for p in self.parts):
            raise ValueError("empty neighborhood class")
        if any(min(a,b)<0 or max(a,b)>=self.n for a,b in self.edges):
            raise ValueError("graph endpoint out of range")
        self.inc = tuple((1<<a)^(1<<b) for a,b in self.edges)
        if canonical(eliminate(self.inc)[1]) != canonical(eliminate(self.cols)[1]):
            raise ValueError("supplied graph does not represent the ordinary columns")
        edge_set={tuple(sorted((a,b))) for a,b in self.edges if a!=b}
        self.adj = [set() for _ in self.parts]
        self.cliques = []
        for i,p in enumerate(self.parts):
            internal = {tuple(sorted(e)) for e in combinations(p,2)}
            if internal & edge_set and not internal <= edge_set:
                raise ValueError("a class is neither independent nor a clique")
            self.cliques.append(internal <= edge_set)
            for j,q in enumerate(self.parts[:i]):
                cross = {tuple(sorted((a,b))) for a in p for b in q}
                if cross <= edge_set:
                    self.adj[i].add(j)
                    self.adj[j].add(i)
                elif cross & edge_set:
                    raise ValueError("class adjacency is not uniform")

    def translate(self, v):
        coeff=solve(self.cols,v)
        if coeff is None:
            raise ValueError("boundary vector outside ordinary span")
        return image(self.inc,coeff)

    def component_bits(self, pattern, colors):
        entries = {}
        num = 0
        for color in range(colors):
            rem={i for i,m in enumerate(pattern) if m>>color & 1}
            while rem:
                i=rem.pop()
                comp={i}
                stack=[i]
                while stack:
                    new=self.adj[stack.pop()] & rem
                    rem.difference_update(new)
                    comp.update(new)
                    stack.extend(new)
                connected=len(comp)>1 or self.cliques[i]
                for j in comp:
                    entries[j,color] = num if connected else None
                num += int(connected)
        return entries

    def realize(self, demands, port, values):
        """Return one support per demand, killed by all prescribed port functionals."""
        demands = tuple(demands)
        if any(solve(self.cols, u) is None for u in demands):
            return None
        if not any(demands):
            return [0] * len(demands)
        values = canonical(values)
        if not values:
            return [solve(self.cols, u) for u in demands]
        demands=tuple(self.translate(u) for u in demands)
        port=tuple(self.translate(v) for v in port)
        r,s,d=len(demands),len(values),len(port)
        q=1<<s
        want=sum(v<<(d*j) for j,v in enumerate(values))
        tbits=[sum(((u>>v)&1)<<j for j,u in enumerate(demands)) for v in range(self.n)]
        pbits=[sum(((u>>v)&1)<<j for j,u in enumerate(port)) for v in range(self.n)]
        options=[[m for m in range(1,1<<q) if m.bit_count()<=len(p)] for p in self.parts]
        for pattern in product(*options):
            comps=self.component_bits(pattern,q)
            table={(0,0):0}
            occupancy=sum(m<<(q*i) for i,m in enumerate(pattern))
            for i,p in enumerate(self.parts):
                allowed=[a for a in range(q) if pattern[i]>>a & 1]
                for v in p:
                    nxt={}
                    for a in allowed:
                        comp=comps[i,a]
                        if comp is None and tbits[v]:
                            continue
                        diff=sum(pbits[v]<<(d*j) for j in range(s) if a>>j & 1)
                        if comp is not None:
                            diff |= tbits[v]<<(d*s+r*comp)
                        mark=1<<(q*i+a)
                        for (bits,seen),colors in table.items():
                            nxt.setdefault((bits^diff,seen|mark),colors|(a<<(s*v)))
                    table=nxt
            assignment=table.get((want,occupancy))
            if assignment is None:
                continue
            vertex=[(assignment>>(s*v))&(q-1) for v in range(self.n)]
            available=[i for i,(a,b) in enumerate(self.edges) if vertex[a]==vertex[b]]
            result=[]
            for u in demands:
                selected=solve(tuple(self.inc[i] for i in available),u)
                assert selected is not None
                result.append(sum(1<<i for j,i in enumerate(available) if selected>>j & 1))
            return result
        return None

    def table(self, local, port):
        if tuple(v for _,v in local)!=self.cols:
            raise ValueError("certified graph must have the same order as the block")
        result={f:{} for f in range(1<<len(port))}
        for f,states in result.items():
            for coord in range(1<<len(port)):
                if (f&coord).bit_count()%2:
                    continue
                u=image(port,coord)
                reps=self.realize((u,),port,(f,))
                if reps is not None:
                    states[u]=sum(1<<idx for j,(idx,_) in enumerate(local) if reps[0]>>j & 1)
        return result

    def exact_kernel(self, roots, K):
        """Return a contracting mask and per-basis ordinary supports, or None."""
        k=len(roots)
        K=canonical(K)
        if any(v>>k for v in K):
            raise ValueError("kernel coordinates exceed the number of named columns")
        demands=tuple(image(roots,kvec) for kvec in K)
        if any(solve(self.cols,u) is None for u in demands):
            return None
        port=intersection(canonical(roots),canonical(self.cols))
        orth=eliminate([sum(((v>>j)&1)<<i for i,v in enumerate(K)) for j in range(k)])[1]
        values=[]
        for z in orth:
            phi=functional(roots,z)
            if phi is None:
                return None
            values.append(sum(((phi&u).bit_count()%2)<<i for i,u in enumerate(port)))
        reps=self.realize(demands,port,values)
        if reps is None:
            return None
        X=0
        for w in reps:
            X |= w
        return X,reps

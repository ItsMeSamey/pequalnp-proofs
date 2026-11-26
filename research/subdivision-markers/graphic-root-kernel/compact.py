"""Target-independent named-kernel reduction for graphic neighborhood classes."""
from collections import Counter, defaultdict
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[1] / "macro-root-states"))
from graphic import GraphicBlock
from macro import canonical, eliminate, image, intersection, solve


def nullspace(rows, n):
    return eliminate([sum(((r>>i)&1)<<j for j,r in enumerate(rows)) for i in range(n)])[1]


def type_data(block, port):
    return {v:(i,sum(((b>>v)&1)<<j for j,b in enumerate(port)))
            for i,part in enumerate(block.parts) for v in part}


def components(n, edges, mask):
    parent=list(range(n))
    def root(i):
        while parent[i]!=i:
            parent[i]=parent[parent[i]]
            i=parent[i]
        return i
    for i,(a,b) in enumerate(edges):
        if mask>>i&1:
            parent[root(a)]=root(b)
    result=defaultdict(list)
    for i in range(n):
        result[root(i)].append(i)
    return list(result.values())


class Compression:
    def __init__(self, original, roots):
        self.original=original
        self.roots=tuple(roots)
        U=intersection(canonical(original.cols),canonical(self.roots))
        self.U=U
        self.dim=len(U)
        self.fullport=tuple(original.translate(v) for v in U)
        self.fulltype=type_data(original,self.fullport)
        groups=defaultdict(list)
        for v,typ in self.fulltype.items():
            groups[typ].append(v)
        limit=2*(self.dim+1)
        keep=[]
        for group in groups.values():
            n=len(group)
            size=n if n<=limit else limit-(n%2)
            keep.extend(group[:size])
        keep.sort()
        idx={v:i for i,v in enumerate(keep)}
        self.reducedtype={i:self.fulltype[v] for i,v in enumerate(keep)}
        parts=[[idx[v] for v in p if v in idx] for p in original.parts]
        edges=tuple(sorted({tuple(sorted((idx[a],idx[b]))) for a,b in original.edges if a in idx and b in idx and a!=b}))
        cols=tuple((1<<a)^(1<<b) for a,b in edges)
        self.reduced=GraphicBlock(cols,edges,len(keep),parts)
        self.smallport=tuple(sum(((v>>old)&1)<<j for j,old in enumerate(keep)) for v in self.fullport)
        assert len(canonical(self.smallport))==self.dim
        named_basis=list(U)
        for b in self.roots:
            if solve(named_basis,b) is None:
                named_basis.append(b)
        self.smallroots=[]
        for b in self.roots:
            coeff=solve(named_basis,b)
            self.smallroots.append(image(self.smallport,coeff)^((coeff>>self.dim)<<len(keep)))

    def transfer(self, mask, back=True):
        if back:
            src,dst=self.reduced,self.original
            tp_src,tp_dst=self.reducedtype,self.fulltype
            port_dst=self.fullport
        else:
            src,dst=self.original,self.reduced
            tp_src,tp_dst=self.fulltype,self.reducedtype
            port_dst=self.smallport
        if mask<0 or mask>>len(src.edges):
            raise ValueError("invalid source edge set")
        rows=[]
        color=[0]*src.n
        for comp in components(src.n,src.edges,mask):
            charge=0
            for v in comp:
                charge^=tp_src[v][1]
            if solve(rows,charge) is None:
                rows.append(charge)
                for v in comp:
                    color[v]=len(rows)
        hist=defaultdict(Counter)
        groups=defaultdict(list)
        for v,typ in tp_src.items():
            hist[typ][color[v]]+=1
        for v,typ in tp_dst.items():
            groups[typ].append(v)
        target=[0]*dst.n
        for typ,group in groups.items():
            counts={c:(1 if val%2 else 2) for c,val in hist[typ].items()}
            leftover=len(group)-sum(counts.values())
            assert leftover>=0 and leftover%2==0
            counts[next(iter(counts))]+=leftover
            it=iter(group)
            for c,size in counts.items():
                for _ in range(size):
                    target[next(it)]=c
        allowed=[i for i,(a,b) in enumerate(dst.edges) if target[a]==target[b]]
        X=0
        for z in nullspace(rows,self.dim):
            take=solve(tuple(dst.inc[i] for i in allowed),image(port_dst,z))
            assert take is not None
            X |= sum(1<<i for j,i in enumerate(allowed) if take>>j&1)
        return X

"""Immutable nonlinear syndrome compiler with a capped, finite wire-join oracle."""
from dataclasses import dataclass


def indices(mask):
    while mask:
        bit=mask&-mask
        yield bit.bit_length()-1
        mask^=bit


def scatter(word,ids):
    return sum(((word>>j)&1)<<i for j,i in enumerate(ids))


def read(word,ids):
    return sum(((word>>i)&1)<<j for j,i in enumerate(ids))


def reduce_word(v,basis):
    coeff=0
    for i in sorted(basis,reverse=True):
        if v>>i&1:
            w,c=basis[i]
            v^=w
            coeff^=c
    return v,coeff


@dataclass(frozen=True)
class Cell:
    group:int
    wires:tuple
    columns:tuple


@dataclass(frozen=True)
class Producer:
    terms:tuple
    effects:tuple
    cells:tuple
    shared:tuple
    private:tuple

    def fiber(self,word):
        fixed=sum(((word>>w)&1)<<v for v,w in self.shared)
        wanted=read(word,tuple(e for c in self.cells for e in c.wires))
        count=0
        first=None
        for private_word in range(1<<len(self.private)):
            x=fixed|scatter(private_word,self.private)
            value=0
            for mon,coef in zip(self.terms,self.effects):
                if x&mon==mon:
                    value^=coef
            if value==wanted:
                count+=1
                if first is None:
                    first=x
        return count,first


@dataclass(frozen=True)
class Test:
    rhs:int
    columns:tuple

    def accepts(self,word):
        value=0
        for w,c in self.columns:
            if word>>w&1:
                value^=c
        return value==self.rhs


@dataclass(frozen=True)
class Network:
    n:int
    equations:tuple
    rhs:int
    producers:tuple
    tests:tuple
    copies:tuple
    unused:tuple
    wires:int


def compile_system(n,equations,rhs,test_groups,producer_monomials):
    """Zero monomial mask denotes one. Scopes partition the surviving nonconstant masks."""
    equations=tuple(tuple(row) for row in equations)
    if n<0 or not 0<=rhs<1<<len(equations):
        raise ValueError("invalid dimensions")
    normalized=[]
    for j,row in enumerate(equations):
        terms=set()
        for m in row:
            if not 0<=m<1<<n:
                raise ValueError("monomial outside raw coordinates")
            terms.symmetric_difference_update([m])
        if 0 in terms:
            rhs^=1<<j
            terms.remove(0)
        normalized.append(tuple(sorted(terms)))
    groups=tuple(tuple(g) for g in test_groups)
    scopes=tuple(tuple(s) for s in producer_monomials)
    if sorted(j for g in groups for j in g)!=list(range(len(equations))):
        raise ValueError("invalid test partition")
    present=set().union(*map(set,normalized))
    if sorted(m for h in scopes for m in h)!=sorted(present):
        raise ValueError("invalid monomial partition")
    reads=[set(v for m in h for v in indices(m)) for h in scopes]
    owners=[[h for h,S in enumerate(reads) if v in S] for v in range(n)]
    nextwire=0
    copies=[]
    input_edges=[[] for h in scopes]
    for v,hs in enumerate(owners):
        if len(hs)>1:
            ws=tuple(range(nextwire,nextwire+len(hs)))
            nextwire+=len(hs)
            copies.append((v,ws))
            for h,w in zip(hs,ws):
                input_edges[h].append((v,w))
    tests=[[] for g in groups]
    producers=[]
    for h,terms in enumerate(scopes):
        cells=[]
        effects=[0]*len(terms)
        shift=0
        for g,rows in enumerate(groups):
            basis={}
            E=[]
            for j,m in enumerate(terms):
                col=sum((m in normalized[row])<<k for k,row in enumerate(rows))
                rem,c=reduce_word(col,basis)
                if rem:
                    coord=1<<len(E)
                    basis[rem.bit_length()-1]=(rem,c^coord)
                    E.append(col)
                    c=coord
                effects[j]|=c<<shift
            ws=tuple(range(nextwire,nextwire+len(E)))
            cells.append(Cell(g,ws,tuple(E)))
            tests[g].extend(zip(ws,E))
            nextwire+=len(E)
            shift+=len(E)
        priv=tuple(v for v in sorted(reads[h]) if len(owners[v])==1)
        producers.append(Producer(terms,tuple(effects),tuple(cells),tuple(input_edges[h]),priv))
    return Network(n,tuple(normalized),rhs,tuple(producers),
                   tuple(Test(read(rhs,g),tuple(ts)) for g,ts in zip(groups,tests)),
                   tuple(copies),tuple(v for v,hs in enumerate(owners) if not hs),nextwire)


def reference_join(net,*,budget):
    """Return None before enumeration if the wire+private trial cap is insufficient."""
    if budget<0:
        raise ValueError("negative budget")
    work=(1<<net.wires)*(1+sum(1<<len(p.private) for p in net.producers))
    if work>budget:
        return None
    total=0
    witness=None
    for w in range(1<<net.wires):
        if any(read(w,ws) not in (0,(1<<len(ws))-1) for _,ws in net.copies):
            continue
        if not all(t.accepts(w) for t in net.tests):
            continue
        ways=1
        raw=0
        for p in net.producers:
            count,x=p.fiber(w)
            if not count:
                ways=0
                break
            ways*=count
            raw|=x
        if ways and witness is None:
            witness=raw
            assert all((sum((raw&m)==m for m in row)&1)==((net.rhs>>i)&1)
                       for i,row in enumerate(net.equations))
        total+=ways
    return total<<len(net.unused),witness

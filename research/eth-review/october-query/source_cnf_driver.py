"""Direct fixed-width/fixed-density CNF entry point, canonical unramified root ring."""
from dataclasses import dataclass
from functools import lru_cache
from packet_layout import SourcePlan
from variable_packet_machine import solve

@lru_cache(None)
def field(s):
    e=4*(s-1).bit_length()
    for lower in range(1,1<<e,2):
        f=(1<<e)|lower
        for d in range(1,e//2+1):
            reducible=False
            for v in range((1<<d)|1,1<<(d+1),2):
                r=f
                while r.bit_length()>=v.bit_length():r^=v<<(r.bit_length()-v.bit_length())
                if not r: reducible=True;break
            if reducible:break
        else:return tuple((f>>i)&1 for i in range(e))
    raise AssertionError('no irreducible lift')

@dataclass(frozen=True)
class Predicate:
    kind:str
    signs:tuple
    birth:int
    extension:int
    def word(self,bits):
        val=(all(b==bits[0] for b in bits) if self.kind=='copy'
             else any(b==sign for b,sign in zip(bits,self.signs,strict=True)))
        return (int(val),)+(0,)*(self.extension-1)

def count(n,clauses):
    """Literals are signed one-based nonzero integers; empty conjunction counts 2^n."""
    if n<0:raise ValueError('negative variable count')
    clean=[]
    for clause in clauses:
        c=set(clause)
        if any(not 1<=abs(v)<=n for v in c):raise ValueError('literal outside range')
        if any(-v in c for v in c):continue
        if not c:return 0
        clean.append(tuple(sorted(c,key=abs)))
    if not clean:return 1<<n
    s=max(2,n+len(clauses));f=field(s);p=n+1
    desc=[];ports=[];links=[]
    def vertex(kind,signs=()):
        desc.append(Predicate(kind,signs,p,len(f)));ports.append([]);return len(desc)-1
    def connect(a,b):
        edge=len(links)
        ports[a].append(2*edge);ports[b].append(2*edge+1);links.append(edge)
    # Ports must follow clause-literal order, including when incidence edges are
    # constructed in variable order below (clean is in increasing abs order).
    occurrence=[[] for _ in range(n)]
    for c in clean:
        v=vertex('clause',tuple(int(z>0) for z in c))
        for z in c:occurrence[abs(z)-1].append(v)
    unused=0
    for batch in occurrence:
        d=len(batch)
        if not d:unused+=1;continue
        chain=[vertex('copy') for _ in range(max(1,d-2))]
        for a,b in zip(chain,chain[1:]):connect(a,b)
        assignment=(chain* d if len(chain)==1 else [chain[0],chain[0],*chain[1:-1],chain[-1],chain[-1]])
        for old,v in zip(batch,assignment,strict=True):connect(old,v)
    m=2*len(links);eq=Predicate('copy',(),p,len(f))
    net=(list(zip(desc,map(tuple,ports))),[(eq,(2*q,2*q+1)) for q in links])
    plan=SourcePlan(s,m,p)
    # Wide fixed-k vertices only exceed the degree cap at finite exceptional root sizes.
    from packet_layout import rounded_power
    if max(map(len,ports))>rounded_power(s):plan=lambda *args:None
    out=solve(net,m,p,f,1,0,plan)
    assert not any(out[1:])
    return (out[0]<<unused)% (1<<p)

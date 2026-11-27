"""Bounded literal adapter from compiled parity networks to the source leaf evaluator."""
from dataclasses import dataclass
from multi_producer_parity import Producer,Test,scatter
from source_cnf_driver import field
from variable_packet_machine import solve
from packet_layout import SourcePlan,rounded_power


@dataclass(frozen=True)
class Entry:
    kind:str
    tensor:object
    edges:tuple
    birth:int
    extension:int

    def word(self,bits):
        if len(bits)!=len(self.edges):
            raise ValueError("wrong native port count")
        if self.kind=='producer':
            value=self.tensor.fiber(scatter(sum(v<<i for i,v in enumerate(bits)),self.edges))[0]
        elif self.kind=='test':
            value=int(self.tensor.accepts(scatter(sum(v<<i for i,v in enumerate(bits)),self.edges)))
        else:
            value=int(len(set(bits))<=1)
        return (value% (1<<self.birth),)+(0,)*(self.extension-1)


def count(net,*,s_cap=8,p_cap=8,wire_cap=8,degree_cap=8,work_cap=10000):
    s=max(net.n,net.wires,2)
    p=net.n+1
    if s>s_cap or p>p_cap or net.wires>wire_cap:
        return None
    left=[('producer',g,tuple(w for _,w in g.shared)+tuple(w for c in g.cells for w in c.wires)) for g in net.producers]
    right=[('test',g,tuple(w for w,_ in g.columns)) for g in net.tests]
    right.extend(('copy',None,ws) for _,ws in net.copies)
    degree=max((len(ws) for _,_,ws in left+right),default=0)
    if degree>min(degree_cap,rounded_power(s)):
        return None
    work=(1<<net.wires)*(1+len(right)+sum(1<<len(g.private) for g in net.producers))
    if work>work_cap:
        return None
    f=field(s)
    plan=SourcePlan(s,net.wires,p)
    if plan.record is not None and net.wires>plan.record[0]:
        return None
    network=tuple(tuple((Entry(kind,g,ws,p,len(f)),ws) for kind,g,ws in side) for side in (left,right))
    result=solve(network,net.wires,p,f,1,0,plan)
    assert not any(result[1:])
    return (result[0]<<len(net.unused))%(1<<p)

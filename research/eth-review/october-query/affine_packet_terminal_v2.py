"""Exact affine support projection for physical Boolean ports with arbitrary residual ring entries."""
from dataclasses import dataclass
from collections import Counter
from packet_entry_tape import canonical_lift

@dataclass(frozen=True)
class LinearEntry:
    arity:int
    equations:tuple
    birth:int
    extension:int
    def __post_init__(self):
        if self.birth<1 or self.extension<1 or self.arity<0 or any(not 0<=a<1<<self.arity or b not in (0,1)
                                                    for a,b in self.equations): raise ValueError('invalid linear gate')
    def word(self,bits):
        if len(bits)!=self.arity: raise ValueError('invalid port count')
        w=sum(b<<i for i,b in enumerate(bits))
        return (int(all((a&w).bit_count()%2==b for a,b in self.equations)),)+(0,)*(self.extension-1)

def rs_first(net,birth,extension):
    B,h=net.B,net.h
    ni=(B//2)*h
    rows=[1<<(ni+j) for j in range(B*h)]
    for j in range(ni):
        c=[0]*(B//2)
        c[j//h]=1<<(j%h)
        for i,t in enumerate(net.constants):
            val=net.eval(c,t)
            for bit in range(h):
                if val>>bit&1: rows[i*h+bit]|=1<<j
    return LinearEntry(ni+B*h,tuple((a,0) for a in rows),birth,extension)

class TerminalCap(Exception): pass

class AffineTerminal:
    """Cap enumerated projected states cumulatively; optional direct old-loop fallback."""
    def __init__(self,state_cap,*,direct_fallback=False):
        if state_cap<0: raise ValueError('invalid cap')
        self.cap=state_cap
        self.direct_fallback=direct_fallback
        self.stats=Counter()
    def __call__(self,network,m,r):
        from source_cnf_driver import Predicate
        if m<0 or any(not 0<=e<m for side in network for _,ports in side for e in ports):
            raise ValueError("invalid physical edge ID")
        p={}
        rest=[]
        seen=set()
        self.stats['leaves']+=1
        for side in network:
            for gate,ports in side:
                if type(gate) is LinearEntry:
                    if len(ports)!=gate.arity or gate.extension!=len(r.f)*r.ell:
                        raise ValueError('affine gate shape mismatch')
                    eqs=gate.equations
                elif type(gate) is Predicate and gate.kind=='copy':
                    if gate.birth<1 or gate.extension!=len(r.f)*r.ell : raise ValueError('invalid COPY')
                    eqs=tuple((1|(1<<i),0) for i in range(1,len(ports)))
                else:
                    rest.append((gate,ports))
                    seen.update(ports)
                    continue
                for mask,b in eqs:
                    a=0
                    while mask:
                        bit=mask&-mask
                        a^=1<<ports[bit.bit_length()-1]
                        mask^=bit
                    while a and a.bit_length()-1 in p:
                        v,t=p[a.bit_length()-1]
                        a^=v
                        b^=t
                    if a: p[a.bit_length()-1]=a,b
                    elif b:
                        self.stats['inconsistent']+=1
                        return r.scalar(0)
        piv=sorted(p.items())
        def complete(x,particular):
            for j,(a,b) in piv:
                if ((x&a).bit_count()%2)^(b if particular else 0): x|=1<<j
            return x
        keep=sum(1<<e for e in seen)
        orig=complete(0,True)&keep
        image={}
        for j in range(m):
            if j in p: continue
            y=complete(1<<j,False)&keep
            while y and y.bit_length()-1 in image: y^=image[y.bit_length()-1]
            if y: image[y.bit_length()-1]=y
        q=len(image)
        d=m-len(p)
        self.stats['max_projection']=max(q,self.stats['max_projection'])
        self.stats['max_support_rank']=max(len(p),self.stats['max_support_rank'])
        self.stats['max_free']=max(d,self.stats['max_free'])
        if d-q>=r.p:
            self.stats['zero_fiber']+=1
            return r.scalar(0)
        size=1<<q
        if size>self.cap-self.stats['states']:
            self.stats['declines']+=1
            if self.direct_fallback: return None
            raise TerminalCap('projected state cap')
        self.stats['states']+=size
        gens=tuple(image.values())
        x=orig
        total=r.scalar(0)
        for i in range(size):
            if i: x^=gens[(i&-i).bit_length()-1]
            v=r.scalar(1)
            for gate,ports in rest:
                value=gate.word(tuple(x>>e&1 for e in ports))
                v=r.mul(v,canonical_lift(value,gate.birth,r.p))
            total=r.add(total,v)
        return r.mul(total,r.scalar(1<<(d-q)))

"""Trace every socket of the 2x2 guarded lookup. Each bit controls one 3-cycle."""
from itertools import product

def transceiver(bit):
    # F=(0 1), F (0 2 1)=(0 2)
    return (2,1,0) if bit else (1,0,2)

def physical(x,y,flags,selectors):
    # Each module owns its own three sockets. Wires are reciprocal or private returns.
    modules={}
    wire={}
    def link(a,b):
        assert a not in wire and b not in wire
        wire[a]=b;wire[b]=a
    for kind,bit in [('R',x),('C',y)]:
        ptr=('ptr',kind)
        modules[ptr]=transceiver(bit)
        link((ptr,0),(ptr,0))
        for k in range(2):link((ptr,1+k),((kind,k),0))
    for k in range(2):
        modules['R',k]=transceiver(selectors>>k&1)
        modules['C',k]=transceiver(selectors>>(2+k)&1)
    for i,j in product(range(2),repeat=2):
        cell=('cell',2*i+j)
        modules[cell]=(1,2,0) if flags>>(2*i+j)&1 else (0,1,2)
        link((cell,0),(('R',i),1+j))
        link((cell,1),(('C',j),1+i))
        link((cell,2),(cell,2))
    p={(v,k):wire[v,q[k]] for v,q in modules.items() for k in range(3)}
    assert len(p)==30 and set(p)==set(p.values())==set(wire)
    src=(('ptr','R'),0);dst=(('ptr','C'),0)
    u=p[src]
    while u!=src and u!=dst:u=p[u]
    return u==dst

if __name__=='__main__':
    joins=0;triples=0
    for x,y,flags in product(range(2),range(2),range(16)):
        target=bool(flags>>(2*x+y)&1)
        found=False
        for s in range(16):
            z=physical(x,y,flags,s)
            mutual=(s>>x&1)==y and (s>>(2+y)&1)==x
            assert z==(target and mutual)
            found|=z;joins+=z
        assert found==target
        if flags==(15^(1<<(2*x+y))):triples+=1;assert not found
    print('1024 full settings,',joins,'joined;',triples,'addressed-hole tables rejected')

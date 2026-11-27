"""Validate a canonical NAND source by exact regeneration, then replay its word."""
from shell_stream import Shell

def compile_source(n,blocks,bridges,suffix=2,*,all_equal=False):
    if n<1 or suffix<2: raise ValueError('invalid size')
    pairs={tuple(sorted((u,v))) for A,B in blocks for u in A for v in B}
    pairs.update(tuple(sorted(e)) for e in bridges)
    if any(u<0 or v>=n or u==v for u,v in pairs): raise ValueError('invalid edge')
    inputs=2*n+1+suffix
    gates=[]
    def nand(a,b):
        gates.append((a,b))
        return inputs+len(gates)-1
    def neg(a):return nand(a,a)
    def both(a,b):return neg(nand(a,b))
    def xor(a,b):
        x=nand(a,b)
        return nand(nand(a,x),nand(b,x))
    t=2*n
    y=t+1
    factors=[xor(y,y+1),neg(xor(y+1,t))]
    for j in range(2,suffix):
        factors.append(neg(xor(y+j,2*((j-2)%n))))
    z=[]
    for u,v in sorted(pairs):
        z.append(both(neg(xor(2*u,2*v)),neg(xor(2*u+1,2*v+1))))
    if all_equal:
        factors.extend(neg(xor(a,z[0])) for a in z[1:])
    else:
        factors.extend(neg(a) for a in z)
    out=factors[0]
    for a in factors[1:]:out=both(out,a)
    return inputs,tuple(gates),out

def solve_source(source,n,blocks,bridges,suffix=2,*,all_equal=False):
    blocks=tuple((tuple(A),tuple(B)) for A,B in blocks)
    bridges=tuple(tuple(e) for e in bridges)
    if source!=compile_source(n,blocks,bridges,suffix,all_equal=all_equal):
        return 'skip',None
    for mask in ((14,1) if all_equal else (14,)):
        shell=Shell(n,[(u,v,mask) for u,v in bridges],
                    [(A,B,mask) for A,B in blocks],[(1,1,1,1)]*n,
                    [15]*n,[0]*(2*n),0,[0]*(2*n),1)
        _,colors=shell.fiber(())
        if colors is None:continue
        raw=[b for c in colors for b in (c&1,c>>1)]
        raw.extend([0,1,0])
        raw.extend(colors[(j-2)%n]&1 for j in range(2,suffix))
        wires=raw[:]
        _,gates,out=source
        for a,b in gates:wires.append(1-(wires[a]&wires[b]))
        if not wires[out]:raise AssertionError('original NAND replay failed')
        return 'sat',tuple(raw)
    return 'unsat',None

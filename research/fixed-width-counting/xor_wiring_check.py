"""Verify the streaming compiler as an actual XOR/AND gate list."""
import random

def span_coordinates(basis):
    result={0:0}
    for i,v in enumerate(basis):
        result.update({x^v:m|(1<<i) for x,m in list(result.items())})
    return result

def compile_graph(rows):
    n=len(rows)
    gates=[]
    zero=n
    def gate(op,i,j):
        gates.append((op,i,j))
        return n+len(gates)
    def combination(wires,mask):
        selected=[v for i,v in enumerate(wires) if mask>>i&1]
        if not selected:
            return zero
        z=selected[0]
        for v in selected[1:]:
            z=gate('xor',z,v)
        return z
    basis=[]; wires=[]; total=zero; width=0
    for i in range(n):
        width=max(width,len(basis))
        prev=span_coordinates(basis)
        mask=(1<<i)-1
        form=combination(wires,prev[rows[i]&mask])
        total=gate('xor',total,gate('and',i,form))
        future=[q&((1<<(i+1))-1) for q in rows[i+1:]]
        lift={0:0}
        # Small-instance reference elimination, by enumerating the linear span.
        for q in future:
            lift.update({z^q:0 for z in list(lift)})
        projection={q&mask:q for q in lift}
        if len(projection)<len(prev):
            p=next(k for k,v in enumerate(basis) if v not in projection)
            for j in range(len(basis)):
                if j!=p and basis[j] not in projection:
                    basis[j]^=basis[p]
                    wires[j]=gate('xor',wires[j],wires[p])
            del basis[p],wires[p]
        for j,b in enumerate(basis):
            basis[j]=projection[b]
            if basis[j]>>i&1:
                wires[j]=gate('xor',wires[j],i)
        if (1<<i) in lift:
            basis.append(1<<i); wires.append(i)
        assert set(span_coordinates(basis))==set(lift)
    assert len(gates)<=n*(3*width+3)
    return gates,total

def evaluate(gates,out,n,x):
    bits=[(x>>i)&1 for i in range(n)]+[0]
    for op,i,j in gates:
        bits.append(bits[i]^bits[j] if op=='xor' else bits[i]&bits[j])
    return bits[out]

rng=random.Random(2026)
count=0
for n in range(2,10):
    for _ in range(15):
        rows=[0]*n
        for i in range(n):
            for j in range(i):
                if rng.randrange(2):
                    rows[i]|=1<<j
                    rows[j]|=1<<i
        gates,out=compile_graph(rows)
        for x in range(1<<n):
            expected=sum((x>>i&1)*(x&rows[i]&((1<<i)-1)).bit_count() for i in range(n))%2
            assert evaluate(gates,out,n,x)==expected
        count+=1
print("Verified compiled phase and gate budget for",count,"graphs on all assignments.")

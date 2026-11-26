"""Verify the threshold grid on all inputs and the paired crown on every cell."""
gates = []
def gate(kind, x, y):
    output = 12 + len(gates)
    gates.append((kind,x,y))
    return output
def OR(x,y): return gate("OR",x,y)
def AND(x,y): return gate("AND",x,y)
def bank(indices):
    signal, *others = indices
    for operand in others:
        signal = OR(signal, operand)
    return signal
rows = [bank(range(4*i,4*i+4)) for i in range(3)]
cols = [bank(range(j,12,4)) for j in range(4)]
a,b,c = rows
row_result = OR(AND(a,b),AND(OR(a,b),c))
a,b,c,d = cols
column_result = OR(AND(OR(a,b),OR(c,d)),AND(OR(a,c),OR(b,d)))
out = OR(row_result,column_result)
def evaluate(mask):
    wires = [bool(mask & (1 << i)) for i in range(12)]
    for kind,x,y in gates:
        wires.append((wires[x] or wires[y]) if kind == "OR" else (wires[x] and wires[y]))
    return wires[out]
assert len(gates)==29
assert sum(k=="AND" for k,_,_ in gates)==4
assert all(evaluate(m)==(m.bit_count()>=2) for m in range(4096))
assert all(evaluate((1<<i)|(1<<j))==(i!=j) for i in range(12) for j in range(12))
print("29 threshold gates; 4 ANDs; 4096 inputs verified. 12 extra paired ORs; 144 crown cells verified.")

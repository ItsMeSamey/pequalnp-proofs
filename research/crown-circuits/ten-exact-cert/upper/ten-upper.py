"""A 24-gate monotone T2 circuit on ten inputs and exhaustive truth-table check."""
gates=[]
def gate(op,a,b):
    gates.append((op,a,b))
    return 9+len(gates)
def three_or(a,b,c):
    return gate("OR",gate("OR",a,b),c)
def two_of_three(a,b,c):
    return gate("OR",gate("AND",a,b),gate("AND",gate("OR",a,b),c))
cells=[gate("OR",0,9),*range(1,9)]
rows=[three_or(*cells[j:j+3]) for j in range(0,9,3)]
cols=[three_or(*cells[j::3]) for j in range(3)]
nine=gate("OR",two_of_three(*rows),two_of_three(*cols))
output=gate("OR",nine,gate("AND",0,9))
assert len(gates)==24
for assignment in range(1024):
    wires=[bool(assignment&(1<<i)) for i in range(10)]
    for op,a,b in gates:
        wires.append((wires[a] and wires[b]) if op=="AND" else (wires[a] or wires[b]))
    assert wires[output]==(assignment.bit_count()>=2)
print("24 gates; 1024/1024 assignments correct")

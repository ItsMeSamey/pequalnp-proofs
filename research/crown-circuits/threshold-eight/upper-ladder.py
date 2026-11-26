"""Validate the splitting construction from arity three through arity eight."""
def threshold(inputs, gates):
    def gate(op,a,b):
        gates.append((op,a,b))
        return len(gates)-1
    if len(inputs)==3:
        a,b,c=inputs
        return gate('or',gate('and',a,b),gate('and',gate('or',a,b),c))
    a,b,*others=inputs
    merged=gate('or',a,b)
    old=threshold([merged,*others],gates)
    return gate('or',old,gate('and',a,b))

for n in range(3,9):
    gates=[('raw',i,i) for i in range(n)]
    output=threshold(list(range(n)),gates)
    assert len(gates)-n==3*n-5
    for assignment in range(1<<n):
        values=[]
        for op,a,b in gates:
            if op=='raw':value=bool(assignment&(1<<a))
            elif op=='and':value=values[a] and values[b]
            else:value=values[a] or values[b]
            values.append(value)
        assert values[output] == (assignment.bit_count()>=2)
    print(n, len(gates)-n, 1<<n)

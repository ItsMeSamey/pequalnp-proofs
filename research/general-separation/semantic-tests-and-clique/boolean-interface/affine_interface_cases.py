"""Frozen scalable families for the affine compiler comparison."""
def case(n, kind):
    names = [f"x{i}" for i in range(n)]
    gates = [["var", x] for x in names]
    def binary(mask, a, b):
        i = len(gates)
        gates.append(["gate", mask, a, b])
        return i
    def parity(seq):
        value = seq[0]
        for x in seq[1:]:
            value = binary(6,value,x)
        return value
    if kind == "permuted":
        a = parity(list(range(n)))
        b = parity(list(reversed(range(n))))
    elif kind == "overlap":
        a = parity(list(range(n-1)))
        b = parity(list(range(1,n)))
    elif kind == "affine_root":
        a = parity(list(range(n)))
        b = parity(list(range(1,n)))
        return {"inputs":names,"gates":gates,"output":binary(6,a,b)}
    else:
        raise ValueError(kind)
    return {"inputs":names,"gates":gates,"output":binary(8,a,b)}

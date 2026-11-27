"""Compile a signed CNF on its declared raw variables to the portfolio gate encoding."""


def compile_cnf(n, clauses):
    """Bit 0 in each affine mask is 1; DIMACS literal i uses mask 1 << abs(i)."""
    if type(n) is not int or n < 0:
        raise ValueError("invalid original variable count")
    gates = []

    def conjunction(left, right):
        if left == 0 or right == 0 or left == right ^ 1:
            return 0
        if left == right or right == 1:
            return left
        if left == 1:
            return right
        gates.append((left, right))
        return 1 << (n + len(gates))

    output = 1
    for clause in clauses:
        literals = set()
        for item in clause:
            if type(item) is not int or item == 0 or abs(item) > n:
                raise ValueError("literal outside declared original input")
            literals.add(item)
        if any(-item in literals for item in literals):
            continue
        all_false = 1
        for item in sorted(literals, key=abs):
            variable = 1 << abs(item)
            false_value = variable ^ (1 if item > 0 else 0)
            all_false = conjunction(all_false, false_value)
        output = conjunction(output, all_false ^ 1)
    return tuple(gates), output


def accepts_cnf(clauses, witness):
    """Direct original evaluator, independent of the translated gate equations."""
    return all(any(bool((witness >> (abs(lit) - 1)) & 1) == (lit > 0)
                   for lit in clause) for clause in clauses)

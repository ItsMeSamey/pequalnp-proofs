"""Build an affine witness map through a given model, allowing cyclic guards."""
from solve import holds


def chart(observed, guards, terminal, model):
    """Return hidden affine forms and observed terminal restrictions.
    Each integer stores coefficients on observations followed by one constant bit.
    """
    n = len(guards)
    constant = 1 << observed
    visible = constant - 1
    if model < 0 or model >= 1 << (observed + n):
        raise ValueError("model outside input domain")
    matrix, rhs = [], []
    hidden = model >> observed
    for i, clause in enumerate(guards):
        if not (hidden >> i) & 1:
            matrix.append(1 << i)
            rhs.append(0)
            continue
        literal = next((lit for lit in clause if holds([lit], model)), None)
        if literal is None:
            raise ValueError("model violates a guard")
        mask, bias = literal
        matrix.append(mask >> observed)
        rhs.append((mask & visible) | ((1 ^ bias) << observed))

    # Switch an active equation by adding 1 xor y_i when its pivot is zero.
    # An inactive row is a unit row and retains pivot one automatically.
    for i in range(n):
        bit = 1 << i
        if not matrix[i] & bit:
            if not hidden & bit:
                raise AssertionError("inactive pivot was not preserved")
            matrix[i] ^= bit
            rhs[i] ^= constant
        for j in range(i + 1, n):
            if matrix[j] & bit:
                matrix[j] ^= matrix[i]
                rhs[j] ^= rhs[i]

    solution = [0] * n
    for i in reversed(range(n)):
        form = rhs[i]
        for j in range(i + 1, n):
            if matrix[i] & (1 << j):
                form ^= solution[j]
        solution[i] = form

    restrictions = []
    for clause in terminal:
        literal = next((lit for lit in clause if holds([lit], model)), None)
        if literal is None:
            raise ValueError("model violates a terminal clause")
        mask, bias = literal
        form = (mask & visible) | (bias << observed)
        for i, yi in enumerate(solution):
            if mask & (1 << (observed + i)):
                form ^= yi
        restrictions.append(form)
    return solution, restrictions


def value(form, observation, observed):
    return (form & (observation | (1 << observed))).bit_count() % 2

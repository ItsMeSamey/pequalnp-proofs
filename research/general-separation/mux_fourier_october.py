"""Exact signed 3-CNF reduction for mixed raw DAGs; supply an exact #SAT callback.

Raw inputs 0..n-1 are MSB first, gates have addresses n+i, -1=0, -2=1.
Rows: ('AND',inputs), ('OR',inputs), ('PARITY',bias,inputs),
('BINARY',table,a,b) with table indexed by 2*a+b, ('MUX',sel,if0,if1).
All fanins may repeat. Empty AND=1, OR=0, PARITY=bias. Even dead gates
must have valid addresses. 'pins' fixes original primary coordinates.

A signed term carries a DIMACS 1-based formula and sign. Sum callback counts
with these signs and divide by 2**(#PARITY). a distinct original selectors
and d AND/OR/PARITY rows require at most 2**(a+d+1) calls. The formula has
O(n+gate_count+1) variables and clauses independent of the raw fanin length:
subcube requirements from many gates merge into at most one unit per variable.
Per-term construction additionally scans all explicit fanin occurrences and
performs polynomial-bit arithmetic. The supplied counter determines runtime.
brute_counter is for tiny tests and is not an implementation of October #SAT.
"""
from dataclasses import dataclass
from primitive_forecast_extractor import _natural


def _bit(x):
    if type(x) not in (int, bool) or x not in (0, 1):
        raise ValueError("expected a bit")
    return int(x)


def _input(n, gates, output, pins):
    _natural(n, "arity")
    rows = []

    def wire(w, end):
        if type(w) is not int or not -2 <= w < end:
            raise ValueError("invalid raw wire")
        return w

    for i, row in enumerate(gates):
        op, *args = row
        end = n + i
        if op in ("AND", "OR") and len(args) == 1:
            normalized = op, tuple(wire(w, end) for w in args[0])
        elif op == "PARITY" and len(args) == 2:
            normalized = op, _bit(args[0]), tuple(wire(w, end) for w in args[1])
        elif op == "BINARY" and len(args) == 3:
            table, a, b = args
            if type(table) is not int or not 0 <= table <= 15:
                raise ValueError("invalid binary truth table")
            normalized = op, table, wire(a, end), wire(b, end)
        elif op == "MUX" and len(args) == 3:
            normalized = (op, *(wire(w, end) for w in args))
        else:
            raise ValueError("invalid gate record")
        rows.append(normalized)
    fixed = []
    for i, bit in pins:
        if type(i) is not int or not 0 <= i < n:
            raise ValueError("invalid primary pin")
        fixed.append((i, _bit(bit)))
    return tuple(rows), wire(output, n + len(rows)), tuple(fixed)


def _parameters(rows):
    selectors = tuple(sorted({g[1] for g in rows if g[0] == "MUX"}))
    d = sum(g[0] in ("AND", "OR", "PARITY") for g in rows)
    denominator = 1 << sum(g[0] == "PARITY" for g in rows)
    return selectors, d, denominator, 1 << (len(selectors) + d + 1)


@dataclass(frozen=True)
class SignedTerm:
    sign: int
    variables: int
    clauses: tuple


def _binary(clauses, a, b, z, table):
    # Forbid each triple inconsistent with z=table(a,b); fold constants and
    # repeated wires at generation time. Positive wire IDs are DIMACS IDs.
    for x in (0, 1):
        for y in (0, 1):
            wrong = 1 ^ ((table >> (2*x + y)) & 1)
            literals = set()
            for w, bit in ((a, x), (b, y), (z, wrong)):
                if w < 0:
                    if -1-w != bit:
                        break
                else:
                    lit = -w if bit else w
                    if -lit in literals:
                        break
                    literals.add(lit)
            else:
                clauses.append(tuple(sorted(literals)))


def _emit(n, rows, out, pins, selectors, d):
    for mask in range(1 << len(selectors)):
        guesses = {w: (mask >> i) & 1 for i, w in enumerate(selectors)}
        mapped = {-1: -1, -2: -2}
        mapped.update((i, i+1) for i in range(n))
        variables = n
        binary = []
        exceptions = []
        for i, row in enumerate(rows):
            op = row[0]
            if op == "MUX":
                z = mapped[row[2 + guesses[row[1]]]]
            else:
                variables += 1
                z = variables
                if op == "BINARY":
                    _, table, a, b = row
                    _binary(binary, mapped[a], mapped[b], z, table)
                else:
                    exceptions.append((op, z, row[1] if op == "PARITY" else 0,
                                       tuple(mapped[w] for w in row[-1])))
            mapped[n+i] = z
        common = [(mapped[w], bit) for w, bit in (*pins, *guesses.items())]
        common.append((mapped[out], 1))
        for choice in range(1 << d):
            requirements = dict()
            valid = True
            character = set()
            phase = 0

            def pin(w, bit):
                nonlocal valid
                if w < 0:
                    valid &= -1-w == bit
                else:
                    valid &= requirements.setdefault(w, bit) == bit

            def toggle(w):
                nonlocal phase
                if w < 0:
                    phase ^= -1-w
                elif w in character:
                    character.remove(w)
                else:
                    character.add(w)

            for w, bit in common:
                pin(w, bit)
            for i, (op, z, bias, inputs) in enumerate(exceptions):
                second = (choice >> i) & 1
                if op == "PARITY":
                    if second:
                        phase ^= bias
                        toggle(z)
                        for w in inputs:
                            toggle(w)
                elif second:
                    phase ^= int(op == "AND")
                    toggle(z)
                    for w in inputs:
                        pin(w, int(op == "AND"))
                else:
                    pin(z, int(op == "OR"))
            if not valid:
                continue
            base = list(binary)
            base.extend((w if bit else -w,) for w, bit in requirements.items())
            for w in character.intersection(requirements):
                phase ^= requirements[w]
            remaining = sorted(character.difference(requirements))
            sign = 1 if phase == 0 else -1
            if not remaining:
                yield SignedTerm(sign, variables, tuple(base))
                continue
            top = variables
            previous = remaining[0]
            for w in remaining[1:]:
                top += 1
                _binary(base, previous, w, top, 6)
                previous = top
            yield SignedTerm(sign, top, tuple(base + [(-previous,)]))
            yield SignedTerm(-sign, top, tuple(base + [(previous,)]))


def terms(n, gates, output, *, pins=(), max_calls=None):
    rows, out, fixed = _input(n, gates, output, pins)
    selectors, d, _, required = _parameters(rows)
    if max_calls is not None and _natural(max_calls, "max_calls") < required:
        raise ValueError("insufficient call budget")
    return _emit(n, rows, out, fixed, selectors, d)


def _execute(n, rows, out, fixed, counter, params):
    selectors, d, denominator, _ = params
    numerator = calls = 0
    for term in _emit(n, rows, out, fixed, selectors, d):
        value = counter(term.variables, term.clauses)
        if type(value) is not int or not 0 <= value <= 1 << term.variables:
            raise ValueError("invalid exact #SAT callback answer")
        numerator += term.sign * value
        calls += 1
    answer, remainder = divmod(numerator, denominator)
    if remainder or not 0 <= answer <= 1 << n:
        raise ValueError("inconsistent exact counts")
    return answer, calls


def _refusal(max_calls, required):
    if max_calls is not None and _natural(max_calls, "max_calls") < required:
        return dict(status="unknown", reason="call_budget", required=required,
                    available=max_calls, calls=0)
    return None


def count(n, gates, output, counter, *, pins=(), max_calls=None):
    rows, out, fixed = _input(n, gates, output, pins)
    params = _parameters(rows)
    required = params[-1]
    refused = _refusal(max_calls, required)
    if refused is not None:
        return refused
    answer, calls = _execute(n, rows, out, fixed, counter, params)
    return dict(status="ok", count=answer, calls=calls, required=required)


def _evaluate(n, rows, out, x):
    bits = {-1: 0, -2: 1}
    bits.update((i, (x >> (n-1-i)) & 1) for i in range(n))
    for i, row in enumerate(rows, n):
        op = row[0]
        if op == "AND":
            result = int(all(bits[w] for w in row[1]))
        elif op == "OR":
            result = int(any(bits[w] for w in row[1]))
        elif op == "PARITY":
            result = row[1]
            for w in row[2]:
                result ^= bits[w]
        elif op == "MUX":
            result = bits[row[2 + bits[row[1]]]]
        else:
            result = (row[1] >> (2*bits[row[2]] + bits[row[3]])) & 1
        bits[i] = result
    return bits[out]


def solve(n, gates, output, counter, *, pins=(), max_calls=None):
    rows, out, fixed = _input(n, gates, output, pins)
    params = _parameters(rows)
    required = (n+1) * params[-1]
    refused = _refusal(max_calls, required)
    if refused is not None:
        return refused
    answer, calls = _execute(n, rows, out, fixed, counter, params)
    if not answer:
        return dict(status="unsat", count=0, calls=calls, required=required)
    x = 0
    prefix = fixed
    for i in range(n):
        zeros, used = _execute(n, rows, out, prefix + ((i, 0),), counter, params)
        calls += used
        bit = int(zeros == 0)
        x = (x << 1) | bit
        prefix += ((i, bit),)
    if not _evaluate(n, rows, out, x) or any(((x >> (n-1-i)) & 1) != b for i, b in fixed):
        raise AssertionError("self-reduced witness failed original evaluation or pins")
    return dict(status="witness", assignment=x, count=answer, calls=calls, required=required)


def brute_counter(variables, clauses):
    """Direct DIMACS enumeration for tiny fixtures, counting every declared bit."""
    return sum(all(any(((x >> (abs(lit)-1)) & 1) == int(lit > 0)
                       for lit in clause) for clause in clauses)
               for x in range(1 << variables))

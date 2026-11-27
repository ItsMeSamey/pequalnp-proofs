"""Canonical, comment-free DIMACS fibres with physical assignment and enable bits.

Challenge variable i uses key bit i-1. Key bit n enables the predictor.
Every encoded CNF itself is unsatisfiable on account of its eight fixed clauses.
parse accepts exactly the canonical byte format emitted by encode.
"""


def _validate_challenge(challenge, n):
    if not isinstance(challenge, (list, tuple)):
        raise ValueError("challenge must be a sequence of signed triples")
    result = []
    for clause in challenge:
        if not isinstance(clause, (tuple, list)) or len(clause) != 3:
            raise ValueError("each challenge clause must have three literals")
        if any(type(lit) is not int or not 1 <= abs(lit) <= n for lit in clause):
            raise ValueError("challenge variable outside the declared range")
        if len({abs(lit) for lit in clause}) != 3:
            raise ValueError("challenge clause must use three distinct variables")
        result.append(tuple(clause))
    return result


def _contradiction(n):
    for mask in range(8):
        yield tuple(-(n + 1 + j) if mask & (1 << j) else n + 1 + j
                    for j in range(3))


def _slot(n, index, bit):
    a = n + 4 + 3 * index
    if bit:
        return (-a, a + 1, a + 2)
    return (a, -(a + 1), a + 2)


def encode(challenge, n, key):
    """Return a strict 3-CNF with the given challenge and n+1 physical key bits."""
    if type(n) is not int or n < 0:
        raise ValueError("n must be a nonnegative integer")
    if type(key) is not int or key < 0 or key.bit_length() > n + 1:
        raise ValueError("key must be a nonnegative integer fitting n+1 bits")
    clauses = _validate_challenge(challenge, n)
    clauses.extend(_contradiction(n))
    clauses.extend(_slot(n, i, (key >> i) & 1) for i in range(n + 1))
    lines = [f"p cnf {4 * n + 6} {len(clauses)}\n"]
    lines.extend(f"{a} {b} {c} 0\n" for a, b, c in clauses)
    return "".join(lines).encode("ascii")


def parse(raw):
    """Return (n, list_of_challenge_triples, key), rejecting malformed byte strings."""
    if type(raw) is not bytes or not raw.endswith(b"\n"):
        raise ValueError("expected canonical DIMACS bytes with a final newline")
    lines = raw[:-1].split(b"\n")
    header = lines[0].split(b" ")
    if len(header) != 4 or header[:2] != [b"p", b"cnf"]:
        raise ValueError("invalid DIMACS header")
    total_variables, total_clauses = map(int, header[2:])
    n, remainder = divmod(total_variables - 6, 4)
    if n < 0 or remainder or total_clauses != len(lines) - 1:
        raise ValueError("inconsistent DIMACS dimensions")
    challenge_length = total_clauses - 8 - (n + 1)
    if challenge_length < 0:
        raise ValueError("missing carrier or key clauses")

    clauses = []
    for line in lines[1:]:
        fields = line.split(b" ")
        if len(fields) != 4 or fields[3] != b"0":
            raise ValueError("expected exactly three literals and a terminator")
        clauses.append(tuple(map(int, fields[:3])))
    challenge = clauses[:challenge_length]
    if clauses[challenge_length:challenge_length + 8] != list(_contradiction(n)):
        raise ValueError("invalid contradiction clauses")
    key = 0
    for i, clause in enumerate(clauses[challenge_length + 8:]):
        bit = int(clause[0] < 0)
        if clause != _slot(n, i, bit):
            raise ValueError("invalid physical key clause")
        key |= bit << i

    # Re-encoding validates the challenge and rejects noncanonical decimal spellings.
    if encode(challenge, n, key) != raw:
        raise ValueError("noncanonical DIMACS representation")
    return n, challenge, key


def predict(raw):
    """Predict one iff enabled and the physical assignment satisfies the challenge."""
    n, challenge, key = parse(raw)
    if not (key >> n) & 1:
        return 0
    return int(all(any(bool((key >> (abs(lit) - 1)) & 1) == (lit > 0)
                       for lit in clause) for clause in challenge))

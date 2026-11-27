"""Physical byte DAG and total real-time DPDA examples for padding_cnf fibres."""
from padding_cnf import encode


def padding_dag(challenge, n):
    """Return (edges, start, final); every edge is (source, byte, destination).

    Exactly the encodings of this challenge over every n+1 bit key are paths.
    Edges point from smaller to larger vertex IDs, including both fork branches.
    """
    zero_lines = encode(challenge, n, 0).splitlines(keepends=True)
    one_lines = encode(challenge, n, (1 << (n + 1)) - 1).splitlines(keepends=True)
    prefix_count = len(zero_lines) - (n + 1)
    edges = []
    current = 0
    for line in zero_lines[:prefix_count]:
        for byte in line:
            edges.append((current, byte, current + 1))
            current += 1
    for left, right in zip(zero_lines[prefix_count:], one_lines[prefix_count:]):
        # A whole marker line is one decision: only these two strings reach join.
        join = current + len(left) + len(right) - 1
        next_vertex = current + 1
        for line in (left, right):
            source = current
            for byte in line[:-1]:
                edges.append((source, byte, next_vertex))
                source = next_vertex
                next_vertex += 1
            edges.append((source, line[-1], join))
        current = join
    return edges, 0, current


def constant_dpda(value):
    """Return (table, initial, bottom, outputs) for the constant raw-byte predictor."""
    if type(value) is not int or value not in (0, 1):
        raise ValueError("constant output must be zero or one")
    table = {(0, 0, byte): (0, "stay") for byte in range(256)}
    return table, 0, 0, {0: value}


def palindrome_dpda(challenge, n):
    """On the fibre accept keys u reverse(u) 1, in low-to-high key bit order.

    This machine also defines an output on every off-fibre byte string. It scans
    a fixed number of prefix lines, then interprets the first signed decimal
    character of each marker. The DAG supplies exact carrier/suffix validation.
    An extra byte after the last line, an incomplete record, a malformed first
    character or a stack mismatch gives output zero. Other line contents are
    ignored by this predictor.
    """
    prefix_lines = encode(challenge, n, 0).count(b"\n") - (n + 1)
    if n % 2:
        raise ValueError("an even number of assignment bits is required")
    first = prefix_lines
    accept = first + 2 * (n + 1)
    reject = accept + 1
    table = {}
    for q in range(reject + 1):
        for top in (0, 1, 2):
            for byte in range(256):
                if q in (accept, reject):
                    action = (reject, "stay")
                elif q < first:
                    action = (q + int(byte == 10), "stay")
                elif (q - first) % 2:
                    action = (q + int(byte == 10), "stay")
                else:
                    i = (q - first) // 2
                    bit = int(byte == 45)
                    if not bit and not 49 <= byte <= 57:
                        action = (reject, "stay")
                    elif i < n // 2:
                        action = (q + 1, "push", bit + 1)
                    elif i < n and top == bit + 1:
                        action = (q + 1, "pop")
                    elif i == n and bit and top == 0:
                        action = (q + 1, "stay")
                    else:
                        action = (reject, "stay")
                table[q, top, byte] = action
    outputs = {q: int(q == accept) for q in range(reject + 1)}
    return table, 0, 0, outputs

"""Two signed matching shells per clause of a DIMACS-literal 3CNF."""
from dataclasses import dataclass

from biclique_total import total_block_witness


@dataclass(frozen=True)
class CNFShell:
    n: int
    encoding: str
    clauses: tuple
    rows: tuple
    ports: tuple
    pins: tuple

    @property
    def shells(self):
        return len(self.rows)

    def lift(self, assignment):
        """Extend an original model to physical bits, or return None for a nonmodel."""
        assignment = tuple(assignment)
        if len(assignment) != self.n or any(v not in (0, 1) for v in assignment):
            raise ValueError("invalid source assignment")
        # Potential 0 is the common rail. Fix its gauge to zero for this lift.
        values = [0, *assignment]
        for clause in self.clauses:
            padded = clause + (clause[-1],) * (3 - len(clause))
            a, b, c = (assignment[abs(lit)-1] ^ (lit < 0) for lit in padded)
            if not (a or b or c):
                return None
            if self.encoding == "centered":
                z = int(not (a or b))
            else:
                z = (1 ^ b) if not a else c
            values.append(z)
        return [values[u] ^ off for u, off in self.ports]

    def decode(self, raw):
        """Validate all physical shells and pins, then replay the source formula."""
        raw = tuple(raw)
        if len(raw) != len(self.ports) or any(v not in (0, 1) for v in raw):
            raise ValueError("invalid raw word")
        if any(raw[a] ^ raw[b] != d for a, b, d in self.pins):
            raise ValueError("violated physical pin")
        if any(raw[a:a+2] == raw[a+2:a+4] for a in range(0, len(raw), 4)):
            raise ValueError("violated physical shell")
        values = {u: v ^ off for (u, off), v in zip(self.ports, raw)}
        rail = values.get(0, 0)
        assignment = [values.get(u, rail) ^ rail for u in range(1, self.n+1)]
        if not all(any(assignment[abs(lit)-1] ^ (lit < 0) for lit in clause)
                   for clause in self.clauses):
            raise AssertionError("original 3CNF replay failed")
        return assignment


def compile_cnf(n, clauses, *, encoding="direct"):
    """Compile clauses of length at most three. An empty clause returns None."""
    if not isinstance(n, int) or n < 0:
        raise ValueError("invalid variable count")
    if encoding not in ("direct", "centered"):
        raise ValueError("expected direct or centered encoding")
    clauses = tuple(tuple(c) for c in clauses)
    if any(len(c) > 3 or any(not isinstance(v, int) or not 1 <= abs(v) <= n
                              for v in c) for c in clauses):
        raise ValueError("invalid signed 3CNF clause")
    if any(not c for c in clauses):
        return None
    rows = []
    ports = []
    last = {}
    pins = []
    for i, clause in enumerate(clauses):
        a, b, c = clause + (clause[-1],) * (3 - len(clause))
        z = n + i + 1
        if encoding == "centered":
            rows.extend([((z, abs(a), 1 ^ (a < 0)), (z, abs(b), 1 ^ (b < 0))),
                         ((z, abs(c), int(c < 0)), (z, 0, 0))])
        else:
            rows.extend([((abs(a), 0, 1 ^ (a < 0)), (z, abs(b), 1 ^ (b < 0))),
                         ((abs(b), 0, 1 ^ (b < 0)), (z, abs(c), int(c < 0)))])
    for ((x, y, d), (u, v, f)) in rows:
        # The two colors are ordered (x,u) and (y XOR 1 XOR d,v XOR 1 XOR f).
        for name, off in ((x, 0), (u, 0), (y, 1 ^ d), (v, 1 ^ f)):
            idx = len(ports)
            if name in last:
                earlier, sign = last[name]
                pins.append((earlier, idx, sign ^ off))
            ports.append((name, off))
            last[name] = idx, off
    return CNFShell(n, encoding, clauses, tuple(rows), tuple(ports), tuple(pins))


def cnf_witness(n, clauses, *, encoding="direct"):
    """Return a replayed source assignment or None on an unsatisfiable formula."""
    chart = compile_cnf(n, clauses, encoding=encoding)
    if chart is None:
        return None
    raw = total_block_witness(chart.shells, chart.pins)
    return None if raw is None else chart.decode(raw)

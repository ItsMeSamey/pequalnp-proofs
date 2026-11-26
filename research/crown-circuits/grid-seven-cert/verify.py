"""Certify the optimum for seven aggregate signals under the 12-crown promise."""
from pathlib import Path
import subprocess
import tempfile


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    gates = []

    def gate(op, a, b):
        gates.append((op, a, b))
        return 23 + len(gates)

    def union(wires):
        value = wires[0]
        for wire in wires[1:]:
            value = gate(0, value, wire)
        return value

    paired = [gate(0, i, 12 + i) for i in range(12)]
    rows = [union(paired[i:i + 4]) for i in (0, 4, 8)]
    cols = [union(paired[i::4]) for i in range(4)]
    require(len(gates) == 29, "Unexpected prefix size")
    prefix = "".join(f"{op} {a} {b}\n" for op, a, b in gates)

    a, b, c = rows
    row_two = gate(0, gate(1, a, b), gate(1, gate(0, a, b), c))
    a, b, c, d = cols
    col_two = gate(0, gate(0, gate(1, a, b), gate(1, c, d)),
                   gate(1, gate(0, a, b), gate(0, c, d)))
    output = gate(0, row_two, col_two)
    require(len(gates) == 41, "Unexpected suffix size")
    positive, negative = [], []
    for i in range(12):
        for j in range(12):
            w = [t in (i, 12 + j) for t in range(24)]
            for op, a, b in gates:
                w.append(w[a] and w[b] if op else w[a] or w[b])
            signature = sum(1 << k for k, wire in enumerate(rows + cols) if w[wire])
            (positive if i != j else negative).append(signature)
            require(w[output] == (i != j), f"Incorrect output on {(i, j)}")
    for k in range(7):
        require(any(p & ~n == 1 << k for p in positive for n in negative),
                f"Missing distinguishing pair for aggregate {k}")
    print("The 12-gate suffix passes all 144 promised inputs.", flush=True)

    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        source = Path(__file__).with_name("token_search.cpp")
        program = root / "verify"
        subprocess.run(["c++", "-std=c++17", "-O3", str(source), "-o", str(program)], check=True)
        (root / "prefix.txt").write_text(prefix)
        line = " ".join(map(str, rows + cols)) + "\n"
        result = subprocess.run([str(program), str(root / "prefix.txt")], input=line,
                                capture_output=True, text=True, check=True)
        require(result.stdout.strip() == "1", "Incomplete lower-bound check")
    print("No suffix of at most 11 binary AND/OR gates on the seven aggregate wires computes the crown.")


if __name__ == "__main__":
    main()

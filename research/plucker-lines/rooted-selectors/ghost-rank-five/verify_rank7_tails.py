"""Produce and verify four independent unrestricted all-tail DRAT certificates."""
import argparse
from contextlib import redirect_stdout
from hashlib import sha256
from io import StringIO
from pathlib import Path
from shutil import which
from subprocess import PIPE, STDOUT, run

import all_tails
from pysat.solvers import Solver


class Capture:
    def __init__(self, name, bootstrap_with):
        self.base = bootstrap_with
        self.pending = []

    def __enter__(self):
        return self

    def __exit__(self, *unused):
        pass

    def add_clause(self, clause):
        self.pending.append(clause)

    def solve(self, assumptions):
        if len(assumptions) != 1 or len(self.pending) != 3:
            raise ValueError("unexpected all-tail selector layout")
        selector, = assumptions
        if any(c[0] != -selector for c in self.pending):
            raise ValueError("selector is missing from a tail clause")
        # Other modes have no positive occurrences of their selectors.
        modes.append(self.base + [c[1:] for c in self.pending])
        self.pending = []
        return False  # collection only


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("output", type=Path)
parser.add_argument("--drat-trim", default="drat-trim")
parser.add_argument("--mode", choices=("00", "01", "10", "11"))
args = parser.parse_args()
checker = which(args.drat_trim)
if checker is None:
    parser.error("drat-trim executable not found")
args.output.mkdir(parents=True, exist_ok=True)

modes = []
all_tails.Solver = Capture
with redirect_stdout(StringIO()):
    all_tails.check(7, induct=False)
if len(modes) != 4:
    raise ValueError("unexpected number of mode formulas")

for name, clauses in zip(("00", "01", "10", "11"), modes):
    if args.mode is not None and args.mode != name:
        continue
    variables = max(abs(x) for c in clauses for x in c)
    cnf = args.output / (name + "-cadical195.cnf")
    proof = args.output / (name + "-cadical195.drat")
    with cnf.open("w") as f:
        f.write(f"p cnf {variables} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
    with Solver(name="cadical195", bootstrap_with=clauses, with_proof=True) as solver:
        if solver.solve() is not False:
            raise ValueError(f"mode {name} is satisfiable")
        trace = solver.get_proof()
    proof.write_text("\n".join(trace) + "\n")
    checked = run([checker, str(cnf), str(proof)], stdout=PIPE, stderr=STDOUT, text=True)
    if checked.returncode or "s VERIFIED" not in checked.stdout:
        raise RuntimeError(checked.stdout)
    print(name, variables, len(clauses), len(trace), sha256(cnf.read_bytes()).hexdigest(),
          sha256(proof.read_bytes()).hexdigest(), "VERIFIED", flush=True)

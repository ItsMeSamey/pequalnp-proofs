"""Record each SAT query and independently check its UNSAT proof with drat-trim."""
import os
import subprocess
import tempfile
from pathlib import Path
from pysat.formula import CNF
from pysat.solvers import Solver

class VerifiedSolver:
    def __init__(self, name):
        self.solver = Solver(name=name, with_proof=True)
        self.formula = CNF()

    def __enter__(self):
        return self

    def __exit__(self, *args):
        self.solver.delete()

    def add_clause(self, literals):
        self.formula.append(literals)

    def append_formula(self, clauses):
        self.formula.extend(clauses)

    def get_model(self):
        return self.solver.get_model()

    def solve_checked(self):
        self.solver.append_formula(self.formula.clauses)
        if self.solver.solve():
            return True
        with tempfile.TemporaryDirectory() as scratch:
            cnf = Path(scratch) / 'instance.cnf'
            proof = Path(scratch) / 'proof.drat'
            self.formula.to_file(str(cnf))
            proof.write_text('\n'.join(self.solver.get_proof())+'\n')
            checked = subprocess.run([os.environ.get('DRAT_TRIM','drat-trim'), str(cnf), str(proof)], capture_output=True, text=True)
            if 's VERIFIED' not in checked.stdout.splitlines():
                raise RuntimeError(checked.stdout+'\n'+checked.stderr)
        return False

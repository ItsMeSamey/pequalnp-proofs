"""Keep CaDiCaL's native DRAT without expanding each proof line into Python strings."""
import sys,shutil
from pathlib import Path
from pysat.formula import CNF
from pysat.solvers import Cadical195,pysolvers
src=Path(sys.argv[1]);out=Path(sys.argv[2])
with Cadical195(bootstrap_with=CNF(from_file=str(src)).clauses,with_proof=True) as solver:
    assert solver.solve() is False
    pysolvers.flushpr(solver.prfp)
    solver.prfile.seek(0)
    with out.open('wb') as f:shutil.copyfileobj(solver.prfile,f,1<<18)
print('native binary DRAT bytes',out.stat().st_size)

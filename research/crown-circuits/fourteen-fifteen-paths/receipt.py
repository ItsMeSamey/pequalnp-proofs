"""Emit a SAT model or native binary DRAT for a frozen CNF."""
from pathlib import Path
from pysat.formula import CNF
from pysat.solvers import Cadical195,pysolvers
import sys,shutil,os
src=Path(sys.argv[1]);dest=Path(sys.argv[2])
with Cadical195(bootstrap_with=CNF(from_file=str(src)).clauses,with_proof=True) as s:
    print('proof temp',os.readlink('/proc/self/fd/'+str(s.prfile.fileno())),flush=True)
    if s.solve():
        (dest/'model.txt').write_text(' '.join(map(str,s.get_model()))+'\n')
        print('SAT')
    else:
        pysolvers.flushpr(s.prfp);s.prfile.seek(0)
        with (dest/'proof.dratb').open('wb') as f:shutil.copyfileobj(s.prfile,f,1<<18)
        print('UNSAT', (dest/'proof.dratb').stat().st_size)

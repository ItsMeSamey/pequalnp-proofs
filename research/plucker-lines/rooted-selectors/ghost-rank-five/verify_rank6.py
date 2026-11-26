from hashlib import sha256
from itertools import product
from pathlib import Path
from subprocess import run,PIPE,STDOUT

import argparse
import shutil

parser=argparse.ArgumentParser(description="Generate and independently verify all 128 rank-six DRAT traces.")
parser.add_argument("output",type=Path)
parser.add_argument("--drat-trim",default="drat-trim")
args=parser.parse_args()
import finite_types
from pysat.solvers import Solver as Backend

output=args.output
output.mkdir(parents=True,exist_ok=True)
checker=shutil.which(args.drat_trim)
if checker is None:
    parser.error("drat-trim executable not found")

class Capture:
    def __init__(self,name,bootstrap_with):
        self.cnf=bootstrap_with
    def __enter__(self):return self
    def __exit__(self,*exc):pass
    def solve(self):
        cnf=self.cnf
        with Backend(name='glucose4',bootstrap_with=cnf,with_proof=True) as solver:
            if solver.solve() is not False:
                raise ValueError(f"Glucose4 failed to refute chart {params}")
            drat=solver.get_proof()
        n=max(abs(v) for c in cnf for v in c)
        dimacs=f'p cnf {n} {len(cnf)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cnf)
        name=''.join(map(str,params))
        f=output/(name+'.cnf');p=output/(name+'.drat')
        f.write_text(dimacs);p.write_text('\n'.join(drat)+'\n')
        result=run([checker,str(f),str(p)],stdout=PIPE,stderr=STDOUT,text=True)
        if result.returncode or 's VERIFIED' not in result.stdout:
            raise RuntimeError((params,result.returncode,result.stdout))
        print(name,len(cnf),len(drat),sha256(f.read_bytes()).hexdigest(),sha256(p.read_bytes()).hexdigest(),'VERIFIED',flush=True)
        return False

finite_types.Solver=Capture
for params in product(range(4),range(4),range(4),range(2)):
    if finite_types.test(6,params) is not None:
        raise ValueError(f"Unexpected SAT chart {params}")

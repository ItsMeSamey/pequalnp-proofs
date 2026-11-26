"""A counterexample lacks every cheap witness on each of its two target arms."""
from itertools import combinations
from pathlib import Path
import sys
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'eight-line-surplus'))
from samples import lines, neg

def counterexample(arms):
    formula = CNF()
    pool = IDPool()
    features = [[pool.id(('feature', i, p)) for p in range(13)] for i in range(5)]
    cache = {}
    def gate(literals, operation):
        literals = tuple(sorted(set(literals)))
        if len(literals) == 1:
            return literals[0]
        key = operation, literals
        if key in cache:
            return cache[key]
        result = pool.id(key)
        cache[key] = result
        if operation == 'AND':
            for x in literals:
                formula.append([-result, x])
            formula.append([result] + [-x for x in literals])
        else:
            for x in literals:
                formula.append([result, -x])
            formula.append([-result, *literals])
        return result

    for t in arms:
        negatives = {q for q,l in neg if (l>>t)&1 and
                     all(q&v for i,v in enumerate(lines) if i not in arms)}
        for q in negatives:
            if any(q != r and not q & ~r for r in negatives):
                continue
            disjoint = [gate((-a for j,a in enumerate(row) if (q>>j)&1), 'AND')
                        for row in features]
            for p in range(13):
                if (lines[t]>>p)&1:
                    formula.append([gate((row[p], d), 'AND') for row,d in zip(features,disjoint)])

    def exclude_cheap_output(row, gates):
        for t in arms:
            inside = [x for p,x in enumerate(row) if (lines[t]>>p)&1]
            outside = [x for p,x in enumerate(row) if not (lines[t]>>p)&1]
            for subset in combinations(inside, gates+2):
                formula.append(outside + [-x for x in subset])

    for row in features:
        exclude_cheap_output(row, 0)
    for r,s in combinations(features, 2):
        for op in ('AND','OR'):
            w = [gate(x,op) for x in zip(r,s)]
            exclude_cheap_output(w, 1)
            for h in features:
                if h in (r,s):
                    continue
                for op2 in ('AND','OR'):
                    exclude_cheap_output([gate(x, op2) for x in zip(w,h)], 2)
    return formula, features

def verify(arms, proof_directory=None):
    cnf, features = counterexample(arms)
    with Solver(name='cadical195', bootstrap_with=cnf.clauses,
                with_proof=proof_directory is not None) as solver:
        if solver.solve():
            model = set(solver.get_model())
            raise ValueError((arms, [sum((x in model)<<p for p,x in enumerate(row))
                                     for row in features]))
        if proof_directory is not None:
            proof_directory.mkdir(exist_ok=True,parents=True)
            stem = ''.join(map(str,arms))
            cnf.to_file(str(proof_directory/(stem+'.cnf')))
            (proof_directory/(stem+'.drat')).write_text('\n'.join(solver.get_proof())+'\n')
        print(arms,cnf.nv,len(cnf.clauses),'UNSAT',flush=True)

if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--proof-directory', type=Path)
    parser.add_argument('pairs', nargs='*')
    args = parser.parse_args()
    for arms in ([tuple(map(int,x)) for x in args.pairs] or combinations(range(7),2)):
        verify(arms, args.proof_directory)
